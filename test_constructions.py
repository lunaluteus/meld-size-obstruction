import unittest

from constructions import sparse_full_wait
from melds import verify_witness


class ConstructionTests(unittest.TestCase):
    def test_all_draws_have_certificates_with_the_advertised_meld_count(self):
        # Covers both suit parities, q=0, ranks=k, and overlapping eye intervals.
        for k in range(2, 15, 2):
            for ranks in range(k, 101):
                for q in range(4):
                    with self.subTest(k=k, ranks=ranks, q=q):
                        hand, witnesses = sparse_full_wait(k, ranks, q)
                        eye = 1+k*q
                        melds = q*(k-1) + (ranks-k+1)//2
                        self.assertEqual(len(hand), ranks)
                        self.assertEqual(len(witnesses), ranks)
                        self.assertEqual(sum(hand)+1, eye+k*melds)
                        for draw, witness in enumerate(witnesses):
                            completed = list(hand)
                            completed[draw] += 1
                            self.assertEqual(len(witness.melds), melds)
                            self.assertTrue(verify_witness(tuple(completed), k, eye, witness))

    def test_small_reference_hand(self):
        hand, _ = sparse_full_wait(4, 6, 1)
        self.assertEqual(hand, (0, 5, 5, 5, 5, 0))

    def test_rejects_parameters_outside_the_construction(self):
        for args in [(1, 4, 1), (3, 6, 1), (4, 3, 1), (4, 8, -1)]:
            with self.subTest(args=args), self.assertRaises(ValueError):
                sparse_full_wait(*args)


if __name__ == '__main__':
    unittest.main()
