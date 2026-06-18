from __future__ import annotations

import asyncio
import random
import socket
from dataclasses import dataclass
from typing import Any

from loguru import logger
from scapy.layers.dns import DNS, DNSQR

_resolvers = None

_DNS_PORT = 53
_RECV_BYTES = 4096
_RESOLVER_GROUPS = (
    ("9.9.9.9", "149.112.112.112"),
    ("1.1.1.1", "1.0.0.1"),
)
_QTYPE_BY_NAME = {
    "A": 1,
    "CNAME": 5,
    "MX": 15,
    "TXT": 16,
    "SRV": 33,
}


class DnsNXDomain(Exception):
    """Raised when a resolver returns NXDOMAIN."""


class DnsTimeout(Exception):
    """Raised when a DNS query times out."""


class DnsNoAnswer(Exception):
    """Raised when a response has no matching answer records."""


class DnsNoNameservers(Exception):
    """Raised when no configured nameserver can answer the query."""


@dataclass(frozen=True)
class DnsName:
    """Small DNS name wrapper used by existing probes."""

    value: str

    def __str__(self) -> str:
        return self.value


@dataclass(frozen=True)
class DnsRecord:
    """Answer adapter exposing the attributes the probe layer consumes."""

    rdtype: str
    value: str = ""
    exchange: DnsName | None = None
    target: DnsName | None = None
    strings: tuple[bytes, ...] = ()

    def __str__(self) -> str:
        return self.value


@dataclass(frozen=True)
class ScapyResolver:
    """DNS resolver that builds/parses packets with Scapy over UDP sockets."""

    nameservers: tuple[str, ...]
    timeout: float = 10.0

    async def resolve(self, qname: str, rdtype: str) -> list[DnsRecord]:
        return await asyncio.to_thread(self._resolve_sync, qname, rdtype)

    def _resolve_sync(self, qname: str, rdtype: str) -> list[DnsRecord]:
        last_timeout = False
        last_no_nameservers = False
        for nameserver in self.nameservers:
            try:
                return _query_nameserver(nameserver, qname, rdtype, self.timeout)
            except DnsNXDomain:
                raise
            except DnsTimeout:
                last_timeout = True
                continue
            except DnsNoNameservers:
                last_no_nameservers = True
                continue

        if last_timeout:
            raise DnsTimeout("all nameservers timed out")
        if last_no_nameservers:
            raise DnsNoNameservers("all nameservers failed")
        raise DnsNoAnswer("all nameservers returned no answer")


def make_resolvers() -> list[ScapyResolver]:
    """Create resolvers for Quad9 and Cloudflare."""
    return [ScapyResolver(nameservers) for nameservers in _RESOLVER_GROUPS]


def get_resolvers() -> list[ScapyResolver]:
    global _resolvers
    if _resolvers is None:
        _resolvers = make_resolvers()
    return _resolvers


async def resolve_robust(qname: str, rdtype: str) -> list[DnsRecord] | None:
    """Universal DNS query with multi-resolver fallback and logging.

    Iterates Quad9 -> Cloudflare resolvers.
    NXDOMAIN is terminal (returns None immediately).
    NoAnswer/NoNameservers are expected (debug-level) and retry next resolver.
    Timeout is a real issue (warning-level) and retries next resolver.
    """
    resolvers = get_resolvers()
    had_timeout = False
    for i, resolver in enumerate(resolvers):
        try:
            return await resolver.resolve(qname, rdtype)
        except DnsNXDomain:
            return None
        except DnsTimeout:
            had_timeout = True
            logger.debug(
                "DNS {}/{}: Timeout on resolver {}, retrying",
                qname,
                rdtype,
                i,
            )
            await asyncio.sleep(0.5)
            continue
        except (DnsNoAnswer, DnsNoNameservers) as e:
            logger.debug(
                "DNS {}/{}: {} on resolver {}, trying next",
                qname,
                rdtype,
                type(e).__name__,
                i,
            )
            await asyncio.sleep(0.5)
            continue
        except Exception as e:
            logger.warning(
                "DNS {}/{}: unexpected error on resolver {}: {}",
                qname,
                rdtype,
                i,
                type(e).__name__,
            )
            continue
    if had_timeout:
        logger.warning("DNS {}/{}: all resolvers exhausted", qname, rdtype)
    else:
        logger.debug("DNS {}/{}: all resolvers exhausted", qname, rdtype)
    return None


def _query_nameserver(
    nameserver: str,
    qname: str,
    rdtype: str,
    timeout: float,
) -> list[DnsRecord]:
    qtype = _QTYPE_BY_NAME[rdtype.upper()]
    query_id = random.randint(0, 0xFFFF)
    query = DNS(id=query_id, rd=1, qd=DNSQR(qname=qname, qtype=qtype))

    try:
        with socket.socket(_socket_family(nameserver), socket.SOCK_DGRAM) as sock:
            sock.settimeout(timeout)
            sock.sendto(bytes(query), (nameserver, _DNS_PORT))
            response_bytes, _ = sock.recvfrom(_RECV_BYTES)
    except TimeoutError as e:
        raise DnsTimeout from e
    except OSError as e:
        raise DnsNoNameservers from e

    response = DNS(response_bytes)
    if response.id != query_id:
        raise DnsNoAnswer("mismatched DNS response id")
    if response.rcode == 3:
        raise DnsNXDomain
    if response.rcode != 0:
        raise DnsNoNameservers(f"rcode={response.rcode}")

    records = _parse_answer_records(response, qtype)
    if not records:
        raise DnsNoAnswer
    return records


def _socket_family(nameserver: str) -> socket.AddressFamily:
    if ":" in nameserver:
        return socket.AF_INET6
    return socket.AF_INET


def _parse_answer_records(response: DNS, qtype: int) -> list[DnsRecord]:
    records: list[DnsRecord] = []
    for rr in _iter_answers(response):
        if int(rr.type) != qtype:
            continue
        record = _adapt_record(rr, qtype)
        if record is not None:
            records.append(record)
    return records


def _iter_answers(response: DNS) -> list[Any]:
    answers = response.an
    if answers is None:
        return []
    if isinstance(answers, list):
        return list(answers)
    try:
        return list(answers)
    except TypeError:
        return [answers]


def _adapt_record(rr: Any, qtype: int) -> DnsRecord | None:
    if qtype == _QTYPE_BY_NAME["A"]:
        return DnsRecord(rdtype="A", value=str(rr.rdata))
    if qtype == _QTYPE_BY_NAME["CNAME"]:
        target = _dns_name(rr.rdata)
        return DnsRecord(rdtype="CNAME", value=str(target), target=target)
    if qtype == _QTYPE_BY_NAME["MX"]:
        exchange = _dns_name(rr.exchange)
        return DnsRecord(rdtype="MX", value=str(exchange), exchange=exchange)
    if qtype == _QTYPE_BY_NAME["TXT"]:
        strings = _txt_strings(rr.rdata)
        return DnsRecord(
            rdtype="TXT",
            value=b"".join(strings).decode("utf-8", errors="ignore"),
            strings=strings,
        )
    if qtype == _QTYPE_BY_NAME["SRV"]:
        target = _dns_name(rr.target)
        return DnsRecord(rdtype="SRV", value=str(target), target=target)
    return None


def _dns_name(value: Any) -> DnsName:
    if isinstance(value, bytes):
        name = value.decode("utf-8", errors="ignore")
    else:
        name = str(value)
    return DnsName(name.rstrip(".").lower() + ".")


def _txt_strings(value: Any) -> tuple[bytes, ...]:
    if isinstance(value, list | tuple):
        return tuple(_ensure_bytes(part) for part in value)
    return (_ensure_bytes(value),)


def _ensure_bytes(value: Any) -> bytes:
    if isinstance(value, bytes):
        return value
    return str(value).encode("utf-8")


async def lookup_mx(domain: str) -> list[str]:
    """Return list of MX exchange hostnames."""
    answer = await resolve_robust(domain, "MX")
    if answer is None:
        return []
    return sorted(str(r.exchange).rstrip(".").lower() for r in answer)
