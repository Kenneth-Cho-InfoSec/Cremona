#!/usr/bin/env python3
"""Exact rational rank for a planar bar-framework rigidity matrix.

The Cremona example emits a compact integer protocol: eight summary integers
followed by the q,r coordinate pairs.  For the triangular lattice, squared
distance is q^2 + q*r + r^2, represented by the metric below.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from typing import Iterable, Sequence


Point = tuple[Fraction, Fraction]
Edge = tuple[int, int]
Metric = tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]


def rigidity_matrix_rank(
    points: Sequence[Point], edges: Iterable[Edge], metric: Metric
) -> int:
    """Return the exact rank over Q of the framework's distance derivative."""
    n = len(points)
    rows: list[list[Fraction]] = []
    for i, j in edges:
        if i == j or not (0 <= i < n and 0 <= j < n):
            raise ValueError(f"invalid edge {(i, j)} for {n} points")
        dx = points[i][0] - points[j][0]
        dy = points[i][1] - points[j][1]
        gx = metric[0][0] * dx + metric[0][1] * dy
        gy = metric[1][0] * dx + metric[1][1] * dy
        row = [Fraction(0) for _ in range(2 * n)]
        row[2 * i] = 2 * gx
        row[2 * i + 1] = 2 * gy
        row[2 * j] = -2 * gx
        row[2 * j + 1] = -2 * gy
        rows.append(row)

    rank = 0
    for col in range(2 * n):
        pivot = next((r for r in range(rank, len(rows)) if rows[r][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        scale = rows[rank][col]
        rows[rank] = [entry / scale for entry in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][col]:
                scale = rows[r][col]
                rows[r] = [a - scale * b for a, b in zip(rows[r], rows[rank])]
        rank += 1
        if rank == len(rows):
            break
    return rank


def run_cremona_protocol(values: Sequence[int]) -> tuple[int, int, int]:
    """Validate the patch output and return (point count, contact count, rank)."""
    if len(values) < 8:
        raise ValueError("expected eight summary integers from Cremona")
    n, pairs, contact_count, min_d2, max_d2, *_degree_histogram = values[:8]
    coords = values[8:]
    if len(coords) != 2 * n:
        raise ValueError(f"expected {2 * n} coordinate integers, found {len(coords)}")
    if pairs != n * (n - 1) // 2:
        raise ValueError("unordered-pair count does not match n")
    points = [(Fraction(coords[2 * i]), Fraction(coords[2 * i + 1])) for i in range(n)]
    edges: list[Edge] = []
    for i in range(n):
        for j in range(i + 1, n):
            dq = points[i][0] - points[j][0]
            dr = points[i][1] - points[j][1]
            d2 = dq * dq + dq * dr + dr * dr
            if d2 == 1:
                edges.append((i, j))
    if len(edges) != contact_count:
        raise ValueError("contact count does not match emitted coordinates")
    if edges and min_d2 != 1:
        raise ValueError("reported minimum squared distance is inconsistent")
    if n == 19 and max_d2 != 16:
        raise ValueError("radius-2 patch should report maximum squared distance 16")
    lattice_metric: Metric = (
        (Fraction(1), Fraction(1, 2)),
        (Fraction(1, 2), Fraction(1)),
    )
    return n, len(edges), rigidity_matrix_rank(points, edges, lattice_metric)


def main() -> int:
    try:
        values = [int(line.strip()) for line in sys.stdin if line.strip()]
        n, contacts, rank = run_cremona_protocol(values)
    except (ValueError, IndexError) as exc:
        print(f"rigidity_rank: {exc}", file=sys.stderr)
        return 2
    print(f"points={n} unit_contacts={contacts} exact_rank={rank} kernel={2*n-rank}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
