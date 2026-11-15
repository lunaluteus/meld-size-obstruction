import itertools
import unittest

from melds import (
    WinWitness,
    residue_candidates,
    residue_signature,
    verify_witness,
    wait_witnesses,
)


def brute_residue_candidates(k, eye_size):
    """Directly quantify over all normalized vectors, draws, and eyes."""
    candidates = set()
    for tail in itertools.product(range(k), repeat=k - 1):
        counts = (0,) + tail
        if all(any(len({(counts[r] + (r == draw) - eye_size * (r == eye)) % k
                            for r in range(k)}) == 1
                       for eye in range(k))
               for draw in range(k)):
            candidates.add(counts)
    return frozenset(candidates)


class ResidueTests(unittest.TestCase):
    def test_intersection_against_exhaustive_quantification(self):
        for k in range(2, 6):
            for eye in range(1, k + 1):
                with self.subTest(k=k, eye=eye):
                    self.assertEqual(residue_candidates(k, eye), brute_residue_candidates(k, eye))

    def test_obstruction_for_larger_meld_sizes(self):
        # This finite check tests the implementation; the unbounded proof is in README.
        for k in range(4, 25):
            for eye in range(1, k + 1):
                with self.subTest(k=k, eye=eye):
                    expected = frozenset({(0,) * k}) if eye % k == 1 else frozenset()
                    self.assertEqual(residue_candidates(k, eye), expected)

    def test_nine_gates_is_an_actual_full_wait(self):
        hand = (3, 1, 1, 1, 1, 1, 1, 1, 3)
        self.assertIn(residue_signature(hand, 3), residue_candidates(3, 2))
        witnesses = wait_witnesses(hand, 3, 2)
        self.assertTrue(all(witness is not None for witness in witnesses))
        for draw, witness in enumerate(witnesses):
            completed = list(hand)
            completed[draw] += 1
            self.assertTrue(verify_witness(tuple(completed), 3, 2, witness))

    def test_natural_four_tile_analogue_fails(self):
        hand = (4, 1, 1, 1, 1, 1, 1, 4)
        witnesses = wait_witnesses(hand, 4, 3)
        self.assertEqual([i + 1 for i, witness in enumerate(witnesses) if witness], [1, 4, 5, 8])
        self.assertFalse(residue_candidates(4, 3))

    def test_allowed_eye_residue_has_actual_examples(self):
        for k in range(4, 9):
            for eye in [1, k + 1, 2 * k + 1]:
                hand = (eye - 1 + k,) + (eye - 1,) * (k - 1)
                witnesses = wait_witnesses(hand, k, eye)
                self.assertTrue(all(witness is not None for witness in witnesses))
                for draw, witness in enumerate(witnesses):
                    completed = list(hand)
                    completed[draw] += 1
                    self.assertTrue(verify_witness(tuple(completed), k, eye, witness))

    def test_certificate_checker_rejects_wrong_decompositions(self):
        self.assertFalse(verify_witness((2, 1, 1), 3, 2, WinWitness(0, (("sequence", 0),))))
        self.assertFalse(verify_witness((2, 1, 1), 3, 2, WinWitness(0, (("sequence", 1),))))
        self.assertFalse(verify_witness((2, 1, 1), 3, 2, WinWitness(0, (("unknown", 0),))))


if __name__ == "__main__":
    unittest.main()
