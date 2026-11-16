#!/usr/bin/env python3
"""Regression tests for exact planar framework rigidity ranks."""

from fractions import Fraction
import unittest

from rigidity_rank import rigidity_matrix_rank


IDENTITY = ((Fraction(1), Fraction(0)), (Fraction(0), Fraction(1)))
LATTICE = ((Fraction(1), Fraction(1, 2)), (Fraction(1, 2), Fraction(1)))


def squared_distance(a, b):
    dx = a[0] - b[0]
    dy = a[1] - b[1]
    return dx * dx + dx * dy + dy * dy


class RigidityRankTests(unittest.TestCase):
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

    def test_generated_radius_two_patch_is_infinitesimally_rigid(self):
        radius = 2
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
        self.assertEqual(len(points), 19)
        self.assertEqual(len(edges), 42)
        self.assertEqual(rigidity_matrix_rank(points, edges, LATTICE), 35)


if __name__ == "__main__":
    unittest.main()
