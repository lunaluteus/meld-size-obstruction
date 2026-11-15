"""Explicit full waits with a fixed meld count for even meld sizes.

Zero-based ranks and unrestricted tile multiplicities. The Lean theorem
`fullWait_sparse` proves this construction for unbounded parameters.
"""

from melds import Hand, WinWitness


def sparse_full_wait(k: int, ranks: int, q: int) -> tuple[Hand, tuple[WinWitness, ...]]:
    """Use eye size 1+k*q and q*(k-1)+ceil((ranks-k)/2) winning melds.

    Returns the waiting hand and one explicit certificate per possible draw.
    This gives an existence bound, not a claim of optimality.
    """
    if k < 2 or k % 2 or ranks < k or q < 0:
        raise ValueError('Require even k >= 2, ranks >= k, and q >= 0.')
    padded = ranks + ranks % 2
    eyes = tuple(range(1, k, 2)) + tuple(range(padded-k, padded-1, 2))
    starts = tuple(range(1, padded-k, 2))
    hand = [0] * ranks
    for eye in eyes:
        hand[eye] += k*q
    for start in starts:
        for rank in range(start, start+k):
            hand[rank] += 1
    witnesses = []
    for draw in range(ranks):
        if draw % 2:
            eye = draw % k
            shifted = set(range(eye, draw, k))
            delta = 1
        else:
            eye = draw + ((padded-1-draw)//k)*k
            shifted = set(range(draw+1, eye, k))
            delta = -1
        melds = tuple(('identical', e) for e in eyes if e != eye for _ in range(q))
        melds += tuple(('sequence', s+delta if s in shifted else s) for s in starts)
        witnesses.append(WinWitness(eye, melds))
    return tuple(hand), tuple(witnesses)
