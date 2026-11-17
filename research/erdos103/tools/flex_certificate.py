#!/usr/bin/env python3
"""Exact checker for a one-sided flex certificate of a lattice patch.

The certificate gives axial velocities v_i and epsilon. For every pair, the
squared distance along p_i(t)=p_i+t*v_i is d2 + linear*t + quadratic*t^2.
All checks use fractions, so a successful run certifies the full interval
0 <= t <= epsilon rather than a floating sample.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

from rigidity_rank import rigidity_matrix_rank


def triangular_patch(radius: int) -> list[tuple[Fraction, Fraction]]:
    return [(Fraction(0), Fraction(0))] + [
        (Fraction(q), Fraction(r))
        for q in range(-radius, radius + 1)
        for r in range(-radius, radius + 1)
        if (q, r) != (0, 0) and -radius <= q + r <= radius
    ]


def squared_distance(a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction]) -> Fraction:
    dq = a[0] - b[0]
    dr = a[1] - b[1]
    return dq * dq + dq * dr + dr * dr


def verify_certificate(data: dict[str, Any]) -> dict[str, Any]:
    radius = int(data["radius"])
    epsilon = Fraction(data["epsilon"])
    points = triangular_patch(radius)
    velocities = [
        (Fraction(q), Fraction(r)) for q, r in data["velocity_axial"]
    ]
    if epsilon <= 0 or len(points) != len(velocities):
        raise ValueError("epsilon must be positive and one velocity is required per point")

    max_d2 = max(squared_distance(a, b) for a in points for b in points)
    unit_contacts = 0
    contact_edges = []
    energy_linear = Fraction(0)
    energy_quadratic = Fraction(0)
    pair_count = 0

    for i, a in enumerate(points):
        for j in range(i + 1, len(points)):
            pair_count += 1
            b = points[j]
            d2 = squared_distance(a, b)
            du = velocities[i][0] - velocities[j][0]
            dv = velocities[i][1] - velocities[j][1]
            linear = (2 * (a[0] - b[0]) + a[1] - b[1]) * du + (
                (a[0] - b[0]) + 2 * (a[1] - b[1])
            ) * dv
            quadratic = du * du + du * dv + dv * dv
            if quadratic < 0:
                raise ValueError(f"negative squared-speed coefficient at pair {(i, j)}")

            energy_linear += linear
            energy_quadratic += quadratic
            if d2 == 1:
                unit_contacts += 1
                contact_edges.append((i, j))
                if linear < 0:
                    raise ValueError(f"unit contact {(i, j)} initially closes")

            change_bound = abs(linear) * epsilon + quadratic * epsilon * epsilon
            if d2 == max_d2:
                if linear != 0 or quadratic != 0:
                    raise ValueError(f"diameter pair {(i, j)} does not stay fixed")
            elif d2 == 1:
                if change_bound > max_d2 - d2:
                    raise ValueError(f"unit pair {(i, j)} could exceed the diameter")
            elif change_bound > min(d2 - 1, max_d2 - d2):
                raise ValueError(f"slack pair {(i, j)} could leave the allowed interval")

    if not any(v != (0, 0) for v in velocities):
        raise ValueError("the certificate velocity is zero")
    if energy_linear <= 0 or energy_quadratic < 0:
        raise ValueError("the pair-energy polynomial is not strictly increasing for t >= 0")

    lattice_metric = (
        (Fraction(1), Fraction(1, 2)),
        (Fraction(1, 2), Fraction(1)),
    )
    rank = rigidity_matrix_rank(points, contact_edges, lattice_metric)
    return {
        "radius": radius,
        "points": len(points),
        "pairs": pair_count,
        "diameter_squared": str(max_d2),
        "unit_contacts": unit_contacts,
        "rigidity_rank": rank,
        "epsilon": str(epsilon),
        "energy_linear": str(energy_linear),
        "energy_quadratic": str(energy_quadratic),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    try:
        result = verify_certificate(json.loads(args.certificate.read_text()))
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
