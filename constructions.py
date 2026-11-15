"""Explicit full waits with a fixed meld count for every meld size.

Zero-based ranks and unrestricted tile multiplicities. The Lean theorem
`fullWait_periodic` proves this construction for unbounded parameters.
"""

from melds import Hand, WinWitness


def sparse_full_wait(k: int, ranks: int, q: int) -> tuple[Hand, tuple[WinWitness, ...]]:
    """Use eye size 1+k*q and the periodic construction's exact meld count.

    Returns the waiting hand and one explicit certificate per possible draw.
    This gives an existence bound, not a claim of optimality.
    """
    if k < 2 or ranks < k or q < 0:
        raise ValueError('Require k >= 2, ranks >= k, and q >= 0.')
    eyes = tuple(r if r % 2 else r+k*((ranks-1-r)//k) for r in range(k))
    starts = tuple(t+1 for t in range(ranks-k) if (t % k) % 2 == 0)
    hand = [0] * ranks
    for eye in eyes:
        hand[eye] += k*q
    for start in starts:
        for rank in range(start, start+k):
            hand[rank] += 1
    witnesses = []
    for draw in range(ranks):
        eye = eyes[draw % k]
        if (draw % k) % 2:
            shifted = set(range(eye, draw, k))
            delta = 1
        else:
            shifted = set(range(draw+1, eye, k))
            delta = -1
        melds = tuple(('identical', e) for e in eyes if e != eye for _ in range(q))
        melds += tuple(('sequence', s+delta if s in shifted else s) for s in starts)
        witnesses.append(WinWitness(eye, melds))
    return tuple(hand), tuple(witnesses)
