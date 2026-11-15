"""Print finite residue checks and explicit generalized Nine Gates witnesses."""

import argparse
import json

from melds import residue_candidates, wait_witnesses


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-meld-size", type=int, default=12)
    args = parser.parse_args()
    if args.max_meld_size < 2:
        parser.error("--max-meld-size must be at least two")
    results = []
    for k in range(2, args.max_meld_size + 1):
        allowed = {
            eye % k: sorted(residue_candidates(k, eye))
            for eye in range(1, k + 1)
            if residue_candidates(k, eye)
        }
        hand = (k,) + (1,) * (2 * k - 2) + (k,)
        witnesses = wait_witnesses(hand, k, k - 1)
        results.append({
            "meld_size": k,
            "eye_residues_passing_necessary_condition": allowed,
            "natural_analogue": {
                "hand": hand,
                "eye_size": k - 1,
                "winning_draw_ranks": [draw + 1 for draw, witness in enumerate(witnesses) if witness],
            },
        })
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
