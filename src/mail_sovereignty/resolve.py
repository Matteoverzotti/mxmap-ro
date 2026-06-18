import asyncio
import json
import re
import ssl
import time
import warnings
from pathlib import Path
from typing import Any
from urllib.parse import urlparse

import httpx
import stamina
from loguru import logger

from mail_sovereignty.constants import (
    CANTON_ABBREVIATIONS,
    CONCURRENCY_POSTPROCESS,
    EMAIL_RE,
    # SKIP_DOMAINS,
    SPARQL_QUERY,
    SPARQL_URL,
    SUBPAGES,
    TYPO3_RE,
)
from mail_sovereignty.dns import lookup_mx
from mail_sovereignty.classifier import classify


ANCPI_GEOJSON_PATH = Path("unitati_administrative.geojson")
ANCPI_GEOJSON_URL = (
    "https://hub.arcgis.com/api/v3/datasets/"
    "466b7199c19f4904831e14bc7f407af9_1/downloads/data"
    "?format=geojson&spatialRefId=4326&where=1%3D1"
)
DOWNLOAD_CHUNK_SIZE = 1024 * 1024


def url_to_domain(url: str) -> str:
    """Extract the base domain from a URL."""
    assert url, "URL must not be empty"

    parsed = urlparse(url if "://" in url else f"https://{url}")
    host = parsed.hostname or ""
    if host.startswith("www."):
        host = host[4:]
    return host

def email_to_domain(email: str) -> str:
    """Extract the domain from an email address."""
    return email.split("@")[1].lower().rstrip("\\/.")


def _slugify_name(name: str) -> set[str]:
    """Generate slug variants for a municipality name (umlaut/accent handling)."""
    raw = name.lower().strip()
    raw = re.sub(r"\s*\(.*?\)\s*", "", raw)

    # German umlaut transliteration
    de = raw.replace("\u00fc", "ue").replace("\u00e4", "ae").replace("\u00f6", "oe")
    # French accent removal
    fr = raw
    for a, b in [
        ("\u00e9", "e"),
        ("\u00e8", "e"),
        ("\u00ea", "e"),
        ("\u00eb", "e"),
        ("\u00e0", "a"),
        ("\u00e2", "a"),
        ("\u00f4", "o"),
        ("\u00ee", "i"),
        ("\u00f9", "u"),
        ("\u00fb", "u"),
        ("\u00e7", "c"),
        ("\u00ef", "i"),
    ]:
        fr = fr.replace(a, b)

    def slugify(s):
        s = re.sub(r"['\u2019`]", "", s)
        s = re.sub(r"[^a-z0-9]+", "-", s)
        return s.strip("-")

    return {slugify(de), slugify(fr), slugify(raw)} - {""}


def guess_domains(name: str, canton: str = "") -> list[str]:
    """Generate a set of plausible domain guesses for a municipality."""

    def _slugs_for(text: str) -> set[str]:
        raw = text.lower().strip()
        raw = re.sub(r"\s*\(.*?\)\s*", "", raw)

        de = raw.replace("\u00fc", "ue").replace("\u00e4", "ae").replace("\u00f6", "oe")
        fr = raw
        for a, b in [
            ("\u00e9", "e"),
            ("\u00e8", "e"),
            ("\u00ea", "e"),
            ("\u00eb", "e"),
            ("\u00e0", "a"),
            ("\u00e2", "a"),
            ("\u00f4", "o"),
            ("\u00ee", "i"),
            ("\u00f9", "u"),
            ("\u00fb", "u"),
            ("\u00e7", "c"),
            ("\u00ef", "i"),
        ]:
            fr = fr.replace(a, b)

        def slugify(s):
            s = re.sub(r"['\u2019`]", "", s)
            s = re.sub(r"[^a-z0-9]+", "-", s)
            return s.strip("-")

        slugs = {slugify(de), slugify(fr), slugify(raw)} - {""}

        # Compound name handling: join all words
        # e.g. "Rüti bei Lyssach" -> "ruetibeilyssach.ch"
        extras = set()
        for variant in [de, fr, raw]:
            joined = slugify(variant).replace("-", "")
            if joined and joined not in slugs:
                extras.add(joined)

        return slugs, extras

    # Split on "/" to generate guesses for each part independently
    parts = [p.strip() for p in name.split("/") if p.strip()]

    all_slugs: set[str] = set()
    all_extras: set[str] = set()

    # Always generate from the full name
    slugs, extras = _slugs_for(name)
    all_slugs |= slugs
    all_extras |= extras

    # Also generate from each "/" part individually
    if len(parts) > 1:
        for part in parts:
            slugs, extras = _slugs_for(part)
            all_slugs |= slugs
            all_extras |= extras

    candidates = set()
    canton_abbrev = CANTON_ABBREVIATIONS.get(canton, "")

    for slug in all_slugs:
        candidates.add(f"{slug}.ch")
        candidates.add(f"gemeinde-{slug}.ch")
        candidates.add(f"commune-de-{slug}.ch")
        candidates.add(f"comune-di-{slug}.ch")
        candidates.add(f"stadt-{slug}.ch")
        if canton_abbrev:
            candidates.add(f"{slug}.{canton_abbrev}.ch")

    for joined in all_extras:
        candidates.add(f"{joined}.ch")

    return sorted(candidates)


def detect_website_mismatch(name: str, website_domain: str) -> bool:
    """Detect if a website domain doesn't match the municipality name.

    Returns True if the domain appears unrelated to the municipality name.
    """
    if not name or not website_domain:
        return False

    domain_lower = website_domain.lower()
    slugs = _slugify_name(name)

    # Handle common prefixes
    prefixes = ["stadt-", "gemeinde-", "commune-de-", "comune-di-"]
    domain_stripped = domain_lower
    for prefix in prefixes:
        if domain_stripped.startswith(prefix):
            domain_stripped = domain_stripped[len(prefix) :]
            break

    # Remove TLD for matching
    domain_base = (
        domain_stripped.rsplit(".", 1)[0] if "." in domain_stripped else domain_stripped
    )
    # Strip canton subdomain: e.g. teufen.ar.ch -> teufen
    parts = domain_base.split(".")
    domain_base_first = parts[0] if parts else domain_base

    for slug in slugs:
        if slug in domain_lower:
            return False
        if slug in domain_stripped:
            return False
        if slug == domain_base_first:
            return False

    # Check if any word from the name (4+ chars) appears in the domain
    raw = name.lower().strip()
    raw = re.sub(r"\s*\(.*?\)\s*", "", raw)
    de = raw.replace("\u00fc", "ue").replace("\u00e4", "ae").replace("\u00f6", "oe")
    fr = raw
    for a, b in [
        ("\u00e9", "e"),
        ("\u00e8", "e"),
        ("\u00ea", "e"),
        ("\u00eb", "e"),
        ("\u00e0", "a"),
        ("\u00e2", "a"),
        ("\u00f4", "o"),
        ("\u00ee", "i"),
        ("\u00f9", "u"),
        ("\u00fb", "u"),
        ("\u00e7", "c"),
        ("\u00ef", "i"),
    ]:
        fr = fr.replace(a, b)

    for variant in [raw, de, fr]:
        words = re.findall(r"[a-z]{4,}", variant)
        for word in words:
            if word in domain_lower:
                return False

    return True


def score_domain_sources(
    sources: dict[str, set[str]],
    name: str,
    website_domain: str,
) -> dict[str, Any]:
    """Score domain sources and pick best domain based on agreement."""
    sources_detail: dict[str, list[str]] = {k: sorted(v) for k, v in sources.items()}

    # Collect all unique domains and which sources found them
    domain_sources: dict[str, list[str]] = {}
    for source_name, domains in sources.items():
        for domain in domains:
            if domain not in domain_sources:
                domain_sources[domain] = []
            domain_sources[domain].append(source_name)

    if not domain_sources:
        return {
            "domain": "",
            "source": "none",
            "confidence": "none",
            "sources_detail": sources_detail,
            "flags": [],
        }

    # Pick domain with most source agreement
    best_domain = max(
        domain_sources,
        key=lambda d: (len(domain_sources[d]), "scrape" in domain_sources[d]),
    )
    best_sources = domain_sources[best_domain]
    source_count = len(best_sources)

    # Determine primary source (in priority order)
    source_priority = ["scrape", "redirect", "wikidata", "guess"]
    source = next((s for s in source_priority if s in best_sources), best_sources[0])

    flags: list[str] = []

    # Determine confidence
    if source_count >= 2:
        confidence = "high"
    elif source == "guess":
        confidence = "low"
        flags.append("guess_only")
    else:
        confidence = "medium"

    # Check for disagreement: only flag when a primary source found domains
    # but none match the best domain. Extra domains from guess or within scrape
    # don't count as disagreement.
    primary_sources = ["scrape", "redirect", "wikidata"]
    for src in primary_sources:
        src_domains = sources.get(src, set())
        if src_domains and best_domain not in src_domains:
            flags.append("sources_disagree")
            if confidence == "high":
                confidence = "medium"
            break

    # Check website mismatch
    if website_domain and detect_website_mismatch(name, website_domain):
        flags.append("website_mismatch")
        if confidence == "high":
            confidence = "medium"

    return {
        "domain": best_domain,
        "source": source,
        "confidence": confidence,
        "sources_detail": sources_detail,
        "flags": flags,
    }


@stamina.retry(
    on=(httpx.HTTPStatusError, httpx.ConnectError, httpx.TimeoutException),
    attempts=3,
    wait_initial=2.0,
)
async def _fetch_sparql(
    client: httpx.AsyncClient, url: str, data: dict, headers: dict
) -> httpx.Response:
    r = await client.post(url, data=data, headers=headers)
    r.raise_for_status()
    return r


async def fetch_wikidata() -> dict[str, dict[str, str]]:
    """Query Wikidata for all Romanian UAT's."""

    logger.info("Fetching UAT's from Wikidata")
    headers = {
        "Accept": "application/sparql-results+json",
        "User-Agent": "MXmap-RO/1.0 (https://github.com/Matteoverzotti/mxmap)",
    }
    async with httpx.AsyncClient(timeout=120) as client:
        r = await _fetch_sparql(client, SPARQL_URL, {"query": SPARQL_QUERY}, headers)
        data = r.json()

    logger.info("Wikidata: {} results", len(data["results"]["bindings"]))

    uats = {}
    for row in data["results"]["bindings"]:
        siruta = row.get("siruta", {}).get("value", "")
        name = row.get("itemLabel", {}).get("value", f"SIRUTA-{siruta}")
        website = row.get("website", {}).get("value", "")
        email = row.get("email", {}).get("value", "")

        if siruta not in uats:
            uats[siruta] = {
                "siruta": siruta,
                "name": name,
                "website": website,
                "email": email,
            }
        else:
            if not uats[siruta]["website"] and website:
                uats[siruta]["website"] = website
            if not uats[siruta]["email"] and email:
                uats[siruta]["email"] = email

    logger.info(
        "Wikidata: {} uats, {} with websites",
        len(uats),
        sum(1 for m in uats.values() if m["website"]),
    )
    return uats


def decrypt_typo3(encoded: str, offset: int = 2) -> str:
    """Decrypt TYPO3 linkTo_UnCryptMailto Caesar cipher.

    TYPO3 encrypts mailto: links with a Caesar shift on three ASCII ranges:
      0x2B-0x3A (+,-./0123456789:)  -- covers . : and digits
      0x40-0x5A (@A-Z)             -- covers @ and uppercase
      0x61-0x7A (a-z)             -- covers lowercase
    Default encryption offset is -2, so decryption is +2 with wrap.
    """
    ranges = [(0x2B, 0x3A), (0x40, 0x5A), (0x61, 0x7A)]
    result = []
    for c in encoded:
        code = ord(c)
        decrypted = False
        for start, end in ranges:
            if start <= code <= end:
                size = end - start + 1
                n = start + (code - start + offset) % size
                result.append(chr(n))
                decrypted = True
                break
        if not decrypted:
            result.append(c)
    return "".join(result)


def _is_valid_domain(domain: str) -> bool:
    """Quick syntactic check — reject domains that will fail DNS lookup."""
    if not domain or len(domain) > 253:
        return False
    if "\\" in domain or "/" in domain:
        return False
    return all(0 < len(label) <= 63 for label in domain.split("."))


def extract_email_domains(html: str) -> set[str]:
    """Extract email domains from HTML, including TYPO3-obfuscated emails."""
    domains = set()

    # simple @ in body
    for email in EMAIL_RE.findall(html):
        domain = email.split("@")[1].lower()
        # if domain not in SKIP_DOMAINS:
        domains.add(domain)

    # mailto:
    for email in re.findall(r'mailto:([^">\s?]+)', html):
        if "@" in email:
            domain = email.split("@")[1].lower().rstrip("\\/.")
            # if domain not in SKIP_DOMAINS:
            domains.add(domain)

    # typo3 obfuscated emails
    for encoded in TYPO3_RE.findall(html):
        for offset in range(-25, 26):
            decoded = decrypt_typo3(encoded, offset)
            decoded = decoded.replace("mailto:", "")
            if "@" in decoded and EMAIL_RE.search(decoded):
                domain = decoded.split("@")[1].lower()
                # if domain not in SKIP_DOMAINS:
                domains.add(domain)
                break

    # user(at)domain.ch and user[at]domain.ch variants
    for match in re.findall(
        r"[\w.-]+\s*[\[(]at[\])]\s*[\w.-]+\.\w+", html, re.IGNORECASE
    ):
        normalized = re.sub(r"\s*[\[(]at[\])]\s*", "@", match, flags=re.IGNORECASE)
        if "@" in normalized:
            domain = normalized.split("@")[1].lower()
            # if domain not in SKIP_DOMAINS:
            domains.add(domain)

    return {d for d in domains if _is_valid_domain(d)}


def build_urls(domain: str) -> list[str]:
    """Build candidate URLs to scrape, trying www. prefix first."""
    domain = domain.strip()
    if domain.startswith(("http://", "https://")):
        parsed = urlparse(domain)
        domain = parsed.hostname or domain
    if domain.startswith("www."):
        bare = domain[4:]
    else:
        bare = domain

    bases = [f"https://www.{bare}", f"https://{bare}"]
    urls = []
    for base in bases:
        urls.append(base + "/")
        for path in SUBPAGES:
            urls.append(base + path)
    return urls


def _is_ssl_error(exc: BaseException) -> bool:
    """Check if an exception (or any in its chain) is an SSL verification error."""
    current: BaseException | None = exc
    while current is not None:
        if isinstance(current, ssl.SSLCertVerificationError):
            return True
        # Some builds wrap the error as a string only
        if "CERTIFICATE_VERIFY_FAILED" in str(current):
            return True
        current = current.__cause__ if current.__cause__ is not current else None
    return False


async def _fetch_insecure(url: str) -> httpx.Response:
    """Fetch a URL with SSL verification disabled (single request)."""
    with warnings.catch_warnings():
        warnings.filterwarnings("ignore", message="Unverified HTTPS request")
        async with httpx.AsyncClient(verify=False) as insecure_client:
            return await insecure_client.get(url, follow_redirects=True, timeout=15)


def _process_scrape_response(
    r: httpx.Response,
    domain: str,
    all_domains: set[str],
    redirect_domain: str | None,
) -> tuple[set[str], str | None]:
    """Extract emails and detect redirects from a scrape response.

    Mutates all_domains in place. Returns updated (all_domains, redirect_domain).
    """
    if r.status_code != 200:
        return all_domains, redirect_domain

    if redirect_domain is None:
        final_domain = url_to_domain(str(r.url))
        if final_domain and final_domain != domain:
            redirect_domain = final_domain
            logger.info("Redirect detected: {} -> {}", domain, redirect_domain)

    domains = extract_email_domains(r.text)
    all_domains |= domains
    return all_domains, redirect_domain


async def scrape_email_domains(
    client: httpx.AsyncClient, domain: str
) -> tuple[set[str], str | None]:
    """Scrape a municipality website for email domains.

    Returns:
        Tuple of (email_domains_found, redirect_target_domain_or_None).
        redirect_target_domain is set when the website redirects to a
        different domain (ignoring www prefix differences).
    """
    if not domain:
        return set(), None

    all_domains = set()
    redirect_domain: str | None = None
    urls = build_urls(domain)

    for url in urls:
        try:
            r = await client.get(url, follow_redirects=True, timeout=15)
        except httpx.ConnectError as exc:
            if _is_ssl_error(exc):
                logger.info("SSL error on {}, retrying without verification", url)
                try:
                    r = await _fetch_insecure(url)
                except Exception as retry_exc:
                    logger.debug("Insecure retry {} failed: {}", url, retry_exc)
                    continue
            else:
                logger.debug("Scrape {} failed: {}", url, exc)
                continue
        except Exception as exc:
            logger.debug("Scrape {} failed: {}", url, exc)
            continue

        all_domains, redirect_domain = _process_scrape_response(
            r, domain, all_domains, redirect_domain
        )
        if all_domains:
            return all_domains, redirect_domain

    return all_domains, redirect_domain


async def resolve_municipality_domain(
    m: dict[str, str],
    client: httpx.AsyncClient,
) -> dict[str, Any]:
    """Resolve a municipality's email domain using multiple sources.

    1. Collect from scrape, wikidata, guess sources
    2. Score agreement to pick best domain
    """
    bfs = m["bfs"]
    name = m["name"]
    canton = m.get("canton", "")

    entry: dict[str, Any] = {
        "bfs": bfs,
        "name": name,
        "canton": canton,
    }

    # 2. Collect from multiple sources
    website_domain = url_to_domain(m.get("website", ""))
    sources: dict[str, set[str]] = {
        "scrape": set(),
        "redirect": set(),
        "wikidata": set(),
        "guess": set(),
    }

    # Scrape website for email addresses
    if website_domain:
        email_domains, redirect_domain = await scrape_email_domains(
            client, website_domain
        )
        for email_domain in email_domains:
            mx = await lookup_mx(email_domain)
            if mx:
                sources["scrape"].add(email_domain)

        # Add redirect target as a source (if it has MX records)
        if redirect_domain:
            mx = await lookup_mx(redirect_domain)
            if mx:
                sources["redirect"].add(redirect_domain)

    # Wikidata website domain
    if website_domain:
        mx = await lookup_mx(website_domain)
        if mx:
            sources["wikidata"].add(website_domain)

    # Guess domains
    for guess in guess_domains(name, canton):
        mx = await lookup_mx(guess)
        if mx:
            sources["guess"].add(guess)

    # 3. Score and pick best
    result = score_domain_sources(sources, name, website_domain or "")
    entry.update(result)

    # Add bfs_only flag if applicable
    if m.get("bfs_only"):
        entry.setdefault("flags", []).append("bfs_only")

    return entry


def ensure_ancpi_geojson(path: Path = ANCPI_GEOJSON_PATH) -> Path:
    """Download the ANCPI GeoJSON cache if it is not already present."""
    if path.exists():
        return path

    tmp_path = path.with_suffix(f"{path.suffix}.tmp")
    logger.info("ANCPI GeoJSON missing; downloading {}", ANCPI_GEOJSON_URL)

    headers = {
        "Accept": "application/geo+json,application/json,*/*",
        "User-Agent": "mxmap-ro/1.0",
        "Referer": "https://open-data-ancpi.hub.arcgis.com/",
    }
    try:
        with httpx.stream(
            "GET",
            ANCPI_GEOJSON_URL,
            headers=headers,
            follow_redirects=True,
            timeout=300,
        ) as response:
            response.raise_for_status()
            with tmp_path.open("wb") as f:
                for chunk in response.iter_bytes(DOWNLOAD_CHUNK_SIZE):
                    f.write(chunk)
        tmp_path.replace(path)
    except Exception:
        tmp_path.unlink(missing_ok=True)
        raise

    logger.info("Downloaded ANCPI GeoJSON to {}", path)
    return path


def fetch_ancpi_uat() -> dict[str, dict[str, str]]:
    """Load the Romanian UAT's from the unitati_administrative.geojson file.
    This file is downloaded from the ANCPI ArcGIS Hub when missing.
    """

    geojson_path = ensure_ancpi_geojson()

    logger.info("Loading UAT's from ANCPI GeoJSON")
    with geojson_path.open(encoding="utf-8") as f:
        data = json.load(f)

    logger.info("ANCPI: {} results", len(data["features"]))

    uats = {}
    for row in data["features"]:
        props = row.get("properties", {})
        siruta = props.get("nationalCode", "")
        name = props.get("name_1", {})

        if siruta not in uats:
            uats[siruta] = {
                "siruta": siruta,
                "name": name,
            }

    return uats

async def scan_uat(uat: dict[str, Any], semaphore: asyncio.Semaphore) -> dict[str, Any]:
    """Scan a single municipality for email provider info."""
    async with semaphore:
        if not uat.get("website") and not uat.get("email"):
            logger.info("Skipping UAT {} ({}): no website or email", uat["siruta"], uat["name"])
            return {
                "siruta": uat["siruta"],
                "name": uat["name"],
                "domain": "",
                "mx": [],
                "spf": "",
                "provider": "none",
                "classification_confidence": 0.0,
                "classification_signals": [],
            }
        
        domain = ""
        if uat.get("email"):
            domain = email_to_domain(uat["email"])
        else:
            domain = url_to_domain(uat["website"])
        # TODO: spf

        classification = await classify(domain)
        
        entry = {
            "siruta": uat["siruta"],
            "name": uat["name"],
            "domain": domain,
            "mx": classification.mx_hosts,
            "spf": classification.spf_raw,
            "provider": classification.provider.value,
            "classification_confidence": round(classification.confidence * 100, 1),
            "classification_signals": [
                signal.model_dump(mode="json") for signal in classification.evidence
            ],
        }
        if classification.gateway:
            entry["gateway"] = classification.gateway
        return entry


async def fetch_uats() -> dict[str, dict[str, str]]:
    """Fetch UAT's from both ANCPI and Wikidata, and merge them."""
    ancpi_uat = fetch_ancpi_uat()

    # Wikidata provides website URLs and email addresses
    wikidata_uat = await fetch_wikidata()

    # Merge: for each ancpi uat, attach Wikidata website and email if available
    uats: dict[str, dict[str, Any]] = {}
    for siruta, item in ancpi_uat.items():
        entry: dict[str, Any] = {
            "siruta": siruta,
            "name": item["name"],
            "website": "",
            "email": "",
        }
        if siruta in wikidata_uat:
            entry["website"] = wikidata_uat[siruta].get("website", "")
            entry["email"] = wikidata_uat[siruta].get("email", "")
        uats[siruta] = entry

    logger.info("Total UATs with website info: {}", sum(1 for m in uats.values() if m["website"]))
    logger.info("Total UATs with email info: {}", sum(1 for m in uats.values() if m["email"]))
    logger.info("UATs with no website or email info: {}", [m["name"] for m in uats.values() if not m["website"] and not m["email"]])

    # Log AUTs in ancpi but missing from Wikidata
    ancpi_only = set(ancpi_uat) - set(wikidata_uat)
    if ancpi_only:
        logger.warning(
            "{} AUTs in ANCPI but missing from Wikidata", len(ancpi_only)
        )
        for siruta in sorted(ancpi_only, key=int):
            m = ancpi_uat[siruta]
            logger.warning("    {:>5}  {}", siruta, m["name"])
            uats[siruta]["siruta_only"] = True

    # Log AUTs in Wikidata but not in BFS (potentially dissolved)
    wikidata_only = set(wikidata_uat) - set(ancpi_uat)
    if wikidata_only:
        logger.warning(
            "{} AUTs in Wikidata but missing from ANCPI", len(wikidata_only)
        )
        for siruta in sorted(wikidata_only, key=int):
            m = wikidata_uat[siruta]
            logger.warning("    {:>5}  {}", siruta, m["name"])

    return uats

async def run(output_path: Path) -> None:
    uats = await fetch_uats()
    total = len(uats)

    print(f"\nScanning {total} UATs for MX/SPF records. This can take a few minutes...")

    semaphore = asyncio.Semaphore(CONCURRENCY_POSTPROCESS)
    tasks = [scan_uat(uat, semaphore) for uat in uats.values()]
    
    results = {}
    for coro in asyncio.as_completed(tasks):
        result = await coro
        logger.info("Scanned UAT {} ({}): domain={} mx={} provider={}",
            result.get("siruta", ""),
            result.get("name", ""),
            result.get("domain", ""),
            result.get("mx", ""),
            result.get("provider", ""),
        )

        results[result["siruta"]] = result

    counts = {}
    for r in results.values():
        provider = r.get("provider", "none")
        counts[provider] = counts.get(provider, 0) + 1
    
    sorted_counts = dict(sorted(counts.items(), key=lambda item: item[1], reverse=True))
    logger.info("--- Email provider classification ---")
    for provider, count in sorted_counts.items():
        logger.info("  {:<20} {:>5}", provider, count)
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(results, f, ensure_ascii=False, indent=2)
    logger.info("Results saved to {}", output_path)


    # results: dict[str, dict[str, Any]] = {}
    # done = 0
    # skipped = 0

    # async with httpx.AsyncClient(
    #     headers={"User-Agent": "mxmap.ch/1.0 (https://github.com/davidhuser/mxmap)"},
    #     follow_redirects=True,
    # ) as shared_client:
    #     tasks = [
    #         _resolve_with_shared_client(m, shared_client)
    #         for m in municipalities.values()
    #     ]

    #     for coro in asyncio.as_completed(tasks):
    #         result = await coro
    #         if result is None:
    #             skipped += 1
    #             continue
    #         results[result["bfs"]] = result
    #         done += 1
    #         counts: dict[str, int] = {}
    #         for r in results.values():
    #             counts[r["source"]] = counts.get(r["source"], 0) + 1
    #         logger.info(
    #             "[{:>4}/{}] {} ({}): domain={} source={} confidence={}",
    #             done,
    #             total,
    #             result["name"],
    #             result["bfs"],
    #             result.get("domain", ""),
    #             result.get("source", ""),
    #             result.get("confidence", ""),
    #         )

    # if skipped:
    #     logger.warning("Skipped {} municipalities due to errors", skipped)

    # # Print summary
    # source_counts: dict[str, int] = {}
    # confidence_counts: dict[str, int] = {}
    # for r in results.values():
    #     source_counts[r["source"]] = source_counts.get(r["source"], 0) + 1
    #     confidence_counts[r["confidence"]] = (
    #         confidence_counts.get(r["confidence"], 0) + 1
    #     )

    # logger.info("--- Domain resolution: {} municipalities ---", len(results))
    # logger.info("By source:")
    # for source in ["override", "wikidata", "scrape", "redirect", "guess", "none"]:
    #     logger.info("  {:<12} {:>5}", source, source_counts.get(source, 0))
    # logger.info("By confidence:")
    # for conf in ["high", "medium", "low", "none"]:
    #     logger.info("  {:<12} {:>5}", conf, confidence_counts.get(conf, 0))

    # # Print flagged entries for review (skip overridden — already confirmed)
    # unreviewed = {
    #     bfs: r for bfs, r in results.items() if bfs not in overrides and r.get("flags")
    # }

    # disagreements = [r for r in unreviewed.values() if "sources_disagree" in r["flags"]]
    # if disagreements:
    #     logger.warning("{} domains with source disagreement:", len(disagreements))
    #     for r in sorted(disagreements, key=lambda x: int(x["bfs"])):
    #         logger.warning(
    #             "  {:>5}  {:<30} {:<20} domain={}  sources={}",
    #             r["bfs"],
    #             r["name"],
    #             r["canton"],
    #             r["domain"],
    #             r.get("sources_detail", {}),
    #         )

    # mismatches = [r for r in unreviewed.values() if "website_mismatch" in r["flags"]]
    # if mismatches:
    #     logger.warning("{} domains with website mismatch:", len(mismatches))
    #     for r in sorted(mismatches, key=lambda x: int(x["bfs"])):
    #         logger.warning(
    #             "  {:>5}  {:<30} {:<20} domain={}",
    #             r["bfs"],
    #             r["name"],
    #             r["canton"],
    #             r["domain"],
    #         )

    # guess_only = [r for r in unreviewed.values() if "guess_only" in r["flags"]]
    # if guess_only:
    #     logger.warning("{} domains resolved by guess only:", len(guess_only))
    #     for r in sorted(guess_only, key=lambda x: int(x["bfs"])):
    #         logger.warning(
    #             "  {:>5}  {:<30} {:<20} domain={}",
    #             r["bfs"],
    #             r["name"],
    #             r["canton"],
    #             r["domain"],
    #         )

    # # Print low confidence and unresolved entries for review
    # low_entries = [
    #     r
    #     for bfs, r in results.items()
    #     if bfs not in overrides and r["confidence"] in ("low", "none")
    # ]
    # if low_entries:
    #     logger.warning("{} domains needing review:", len(low_entries))
    #     for r in sorted(low_entries, key=lambda x: int(x["bfs"])):
    #         logger.warning(
    #             "  {:>5}  {:<30} {:<20} domain={}  source={}",
    #             r["bfs"],
    #             r["name"],
    #             r["canton"],
    #             r["domain"] or "(none)",
    #             r["source"],
    #         )

    # sorted_results = dict(sorted(results.items(), key=lambda kv: int(kv[0])))

    # output = {
    #     "generated": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    #     "total": len(results),
    #     "municipalities": sorted_results,
    # }

    # with open(output_path, "w", encoding="utf-8") as f:
    #     json.dump(output, f, ensure_ascii=False, indent=2)

    # size_kb = len(json.dumps(output, ensure_ascii=False)) / 1024
    # logger.info("Wrote {} ({} KB)", output_path, size_kb)
