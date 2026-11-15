"""Explore equal-size identical groups and consecutive-rank melds.

Ranks and residue indices are zero based. An eye consists of `eye_size`
identical tiles. Multiplicities are unrestricted; no four-copy rule applies.
"""

from dataclasses import dataclass
from functools import cache

Hand = tuple[int, ...]
Meld = tuple[str, int]


def normalize(values: Hand, modulus: int) -> Hand:
    """Represent a residue vector modulo addition of a constant vector."""
    return tuple((value - values[0]) % modulus for value in values)


def residue_signature(hand: Hand, meld_size: int) -> Hand:
    counts = [0] * meld_size
    for rank, count in enumerate(hand):
        counts[rank % meld_size] += count
    return normalize(tuple(counts), meld_size)


def residue_candidates(meld_size: int, eye_size: int) -> frozenset[Hand]:
    """Necessary residue signatures for a full wait, not actual winning hands.

    For each draw residue i, a winning eye of residue j requires
    C + e_i - eye_size * e_j to have constant coordinates modulo meld_size.
    Normalize to first coordinate zero, then intersect the allowed signatures.
    """
    _check_sizes(meld_size, eye_size)
    intersection = None
    for draw in range(meld_size):
        allowed = set()
        for eye in range(meld_size):
            counts = [0] * meld_size
            counts[eye] += eye_size
            counts[draw] -= 1
            allowed.add(normalize(tuple(counts), meld_size))
        intersection = allowed if intersection is None else intersection & allowed
    return frozenset(intersection)


@dataclass(frozen=True)
class WinWitness:
    eye_rank: int
    melds: tuple[Meld, ...]


def winning_decomposition(hand: Hand, meld_size: int, eye_size: int) -> WinWitness | None:
    _check_sizes(meld_size, eye_size)
    if not hand or any(count < 0 for count in hand):
        raise ValueError("A hand must have at least one rank and nonnegative counts.")
    for rank, count in enumerate(hand):
        if count < eye_size:
            continue
        remainder = list(hand)
        remainder[rank] -= eye_size
        melds = _decompose(tuple(remainder), meld_size)
        if melds is not None:
            return WinWitness(rank, melds)
    return None


@cache
def _decompose(hand: Hand, meld_size: int) -> tuple[Meld, ...] | None:
    first = next((rank for rank, count in enumerate(hand) if count), None)
    if first is None:
        return ()
    if hand[first] >= meld_size:
        remainder = list(hand)
        remainder[first] -= meld_size
        tail = _decompose(tuple(remainder), meld_size)
        if tail is not None:
            return (("identical", first),) + tail
    if first + meld_size <= len(hand) and all(hand[first:first + meld_size]):
        remainder = list(hand)
        for rank in range(first, first + meld_size):
            remainder[rank] -= 1
        tail = _decompose(tuple(remainder), meld_size)
        if tail is not None:
            return (("sequence", first),) + tail
    return None


def wait_witnesses(hand: Hand, meld_size: int, eye_size: int) -> tuple[WinWitness | None, ...]:
    witnesses = []
    for draw in range(len(hand)):
        completed = list(hand)
        completed[draw] += 1
        witnesses.append(winning_decomposition(tuple(completed), meld_size, eye_size))
    return tuple(witnesses)


def verify_witness(hand: Hand, meld_size: int, eye_size: int, witness: WinWitness) -> bool:
    """Check a completed-hand certificate by reconstructing its tile counts."""
    if not 0 <= witness.eye_rank < len(hand):
        return False
    reconstructed = [0] * len(hand)
    reconstructed[witness.eye_rank] += eye_size
    for kind, start in witness.melds:
        if kind == "identical" and 0 <= start < len(hand):
            reconstructed[start] += meld_size
        elif kind == "sequence" and 0 <= start <= len(hand) - meld_size:
            for rank in range(start, start + meld_size):
                reconstructed[rank] += 1
        else:
            return False
    return tuple(reconstructed) == hand


def _check_sizes(meld_size: int, eye_size: int) -> None:
    if meld_size < 2 or eye_size < 1:
        raise ValueError("Meld size must be at least two and eye size positive.")
