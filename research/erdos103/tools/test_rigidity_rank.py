#!/usr/bin/env python3
"""Regression tests for exact planar framework rigidity ranks."""

from fractions import Fraction
import unittest

from rigidity_rank import rigidity_matrix_rank, run_cremona_protocols


IDENTITY = ((Fraction(1), Fraction(0)), (Fraction(0), Fraction(1)))
LATTICE = ((Fraction(1), Fraction(1, 2)), (Fraction(1, 2), Fraction(1)))


def squared_distance(a, b):
    dx = a[0] - b[0]
    dy = a[1] - b[1]
    return dx * dx + dx * dy + dy * dy


class RigidityRankTests(unittest.TestCase):
    def test_protocol_parses_concatenated_patch_blocks(self):
        triangle_block = [3, 3, 3, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1]
        self.assertEqual(
            run_cremona_protocols(triangle_block + triangle_block),
            [(3, 3, 3), (3, 3, 3)],
        )

    def test_protocol_rejects_a_truncated_block(self):
        with self.assertRaisesRegex(ValueError, "incomplete patch block"):
            run_cremona_protocols([19, 171])

    def test_rigid_unit_triangle_has_rank_three(self):
        points = [(Fraction(0), Fraction(0)), (Fraction(1), Fraction(0)), (Fraction(0), Fraction(1))]
        edges = [(0, 1), (0, 2), (1, 2)]
        self.assertEqual(rigidity_matrix_rank(points, edges, IDENTITY), 3)

    def test_unbraced_unit_square_cycle_has_one_flex(self):
        points = [
            (Fraction(0), Fraction(0)),
            (Fraction(1), Fraction(0)),
            (Fraction(1), Fraction(1)),
            (Fraction(0), Fraction(1)),
        ]
        edges = [(0, 1), (1, 2), (2, 3), (3, 0)]
        self.assertEqual(rigidity_matrix_rank(points, edges, IDENTITY), 4)

    def test_generated_triangular_patches_are_infinitesimally_rigid(self):
        expected = {2: (19, 42, 35), 3: (37, 90, 71), 4: (61, 156, 119)}
        for radius, (expected_points, expected_edges, expected_rank) in expected.items():
            with self.subTest(radius=radius):
                points = [(0, 0)] + [
                    (q, r)
                    for q in range(-radius, radius + 1)
                    for r in range(-radius, radius + 1)
                    if (q, r) != (0, 0) and -radius <= q + r <= radius
                ]
                edges = [
                    (i, j)
                    for i in range(len(points))
                    for j in range(i + 1, len(points))
                    if squared_distance(points[i], points[j]) == 1
                ]
                self.assertEqual(len(points), expected_points)
                self.assertEqual(len(edges), expected_edges)
                self.assertEqual(
                    rigidity_matrix_rank(points, edges, LATTICE), expected_rank
                )


if __name__ == "__main__":
    unittest.main()
