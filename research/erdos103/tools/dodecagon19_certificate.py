#!/usr/bin/env python3
"""Verify the dodecagon + rotated hexagon + center 19-point construction.

Input is Cremona's integer descriptor stream: n followed by n pairs (ring,
index). All coordinates and squared-distance comparisons are evaluated
exactly in Q(sqrt(2), sqrt(3)); no floating-point arithmetic is used.
"""

from __future__ import annotations

import json
from math import isqrt
import sys
from dataclasses import dataclass
from fractions import Fraction
from functools import cmp_to_key


@dataclass(frozen=True)
class BiQuadratic:
    """a + b*sqrt(2) + c*sqrt(3) + d*sqrt(6), with rational coefficients."""

    coeffs: tuple[Fraction, Fraction, Fraction, Fraction]

    def __add__(self, other: BiQuadratic) -> BiQuadratic:
        return BiQuadratic(tuple(a + b for a, b in zip(self.coeffs, other.coeffs)))

    def __neg__(self) -> BiQuadratic:
        return BiQuadratic(tuple(-a for a in self.coeffs))

    def __sub__(self, other: BiQuadratic) -> BiQuadratic:
        return self + -other

    def __mul__(self, other: BiQuadratic) -> BiQuadratic:
        # Basis indices are 1, 2, 3, 6. Their products reduce by square factors.
        radicands = (1, 2, 3, 6)
        out = [Fraction(0) for _ in range(4)]
        for i, left in enumerate(self.coeffs):
            for j, right in enumerate(other.coeffs):
                product = radicands[i] * radicands[j]
                square = max(
                    q for q in range(1, isqrt(product) + 1) if product % (q * q) == 0
                )
                radicand = product // (square * square)
                out[radicands.index(radicand)] += left * right * square
        return BiQuadratic(tuple(out))

    def scale(self, value: int | Fraction) -> BiQuadratic:
        q = Fraction(value)
        return BiQuadratic(tuple(q * a for a in self.coeffs))


ZERO = BiQuadratic((Fraction(0),) * 4)
ONE = BiQuadratic((Fraction(1), Fraction(0), Fraction(0), Fraction(0)))
SQRT2 = BiQuadratic((Fraction(0), Fraction(1), Fraction(0), Fraction(0)))
SQRT3 = BiQuadratic((Fraction(0), Fraction(0), Fraction(1), Fraction(0)))
SQRT6 = BiQuadratic((Fraction(0), Fraction(0), Fraction(0), Fraction(1)))


def qsqrt3_sign(a: Fraction, c: Fraction) -> int:
    """Exact sign of a+c*sqrt(3) for rational a,c."""
    if c == 0:
        return (a > 0) - (a < 0)
    if a == 0 or (a > 0) == (c > 0):
        return (c > 0) - (c < 0)
    comparison = a * a - 3 * c * c
    if comparison == 0:
        raise ArithmeticError("nonzero rational coefficients cannot satisfy a^2=3c^2")
    if a > 0:  # a>0, c<0
        return 1 if comparison > 0 else -1
    # a<0, c>0
    return 1 if comparison < 0 else -1


def format_qsqrt3(value: BiQuadratic) -> str:
    a, b, c, d = value.coeffs
    if b or d:
        raise ValueError(f"squared distance did not reduce to Q(sqrt(3)): {value}")
    if c == 0:
        return str(a)
    if a == 0:
        return f"{c}*sqrt(3)"
    return f"{a} {'+' if c > 0 else '-'} {abs(c)}*sqrt(3)"


def descriptor_points(tokens: list[int]) -> list[tuple[BiQuadratic, BiQuadratic]]:
    if not tokens:
        raise ValueError("empty Cremona output")
    n = tokens[0]
    if n != 19 or len(tokens) != 1 + 2 * n:
        raise ValueError("expected header 19 followed by exactly 19 ring/index pairs")
    descriptors = list(zip(tokens[1::2], tokens[2::2]))
    expected = [(0, i) for i in range(12)] + [(1, i) for i in range(6)] + [(2, 0)]
    if descriptors != expected:
        raise ValueError("ring/index descriptors do not encode the specified 12+6+1 pattern")

    sqrt2 = SQRT2
    sqrt3 = SQRT3
    sqrt6 = SQRT6
    radius = (sqrt6 + sqrt2).scale(Fraction(1, 2))

    outer_directions = [
        (ONE, ZERO),
        (sqrt3.scale(Fraction(1, 2)), ONE.scale(Fraction(1, 2))),
        (ONE.scale(Fraction(1, 2)), sqrt3.scale(Fraction(1, 2))),
        (ZERO, ONE),
        (-ONE.scale(Fraction(1, 2)), sqrt3.scale(Fraction(1, 2))),
        (-sqrt3.scale(Fraction(1, 2)), ONE.scale(Fraction(1, 2))),
        (-ONE, ZERO),
        (-sqrt3.scale(Fraction(1, 2)), -ONE.scale(Fraction(1, 2))),
        (-ONE.scale(Fraction(1, 2)), -sqrt3.scale(Fraction(1, 2))),
        (ZERO, -ONE),
        (ONE.scale(Fraction(1, 2)), -sqrt3.scale(Fraction(1, 2))),
        (sqrt3.scale(Fraction(1, 2)), -ONE.scale(Fraction(1, 2))),
    ]
    inner_directions = [
        ((sqrt6 + sqrt2).scale(Fraction(1, 4)), (sqrt6 - sqrt2).scale(Fraction(1, 4))),
        ((sqrt6 - sqrt2).scale(Fraction(1, 4)), (sqrt6 + sqrt2).scale(Fraction(1, 4))),
        (-sqrt2.scale(Fraction(1, 2)), sqrt2.scale(Fraction(1, 2))),
        (-(sqrt6 + sqrt2).scale(Fraction(1, 4)), -(sqrt6 - sqrt2).scale(Fraction(1, 4))),
        (-(sqrt6 - sqrt2).scale(Fraction(1, 4)), -(sqrt6 + sqrt2).scale(Fraction(1, 4))),
        (sqrt2.scale(Fraction(1, 2)), -sqrt2.scale(Fraction(1, 2))),
    ]
    points = []
    for ring, index in descriptors:
        if ring == 0:
            x, y = outer_directions[index]
            points.append((radius * x, radius * y))
        elif ring == 1:
            points.append(inner_directions[index])
        else:
            points.append((ZERO, ZERO))
    return points


def verify_tokens(tokens: list[int]) -> dict[str, object]:
    points = descriptor_points(tokens)
    distances: list[BiQuadratic] = []
    for i, (x1, y1) in enumerate(points):
        for x2, y2 in points[i + 1 :]:
            dx = x1 - x2
            dy = y1 - y2
            d2 = dx * dx + dy * dy
            if d2.coeffs[1] or d2.coeffs[3]:
                raise ValueError("squared distance unexpectedly uses sqrt(2) or sqrt(6)")
            distances.append(d2)

    lower = ONE
    upper = BiQuadratic((Fraction(8), Fraction(0), Fraction(4), Fraction(0)))
    for d2 in distances:
        a, _, c, _ = d2.coeffs
        if qsqrt3_sign(a - 1, c) < 0:
            raise ValueError(f"pair violates unit separation: {format_qsqrt3(d2)}")
        if qsqrt3_sign(upper.coeffs[0] - a, upper.coeffs[2] - c) < 0:
            raise ValueError(f"pair exceeds the claimed diameter: {format_qsqrt3(d2)}")

    contacts = sum(d2 == lower for d2 in distances)
    diameters = sum(d2 == upper for d2 in distances)
    if contacts != 36 or diameters != 6:
        raise ValueError(f"unexpected contact/diameter counts: {contacts}/{diameters}")

    classes: dict[BiQuadratic, int] = {}
    for d2 in distances:
        classes[d2] = classes.get(d2, 0) + 1

    def compare(left: BiQuadratic, right: BiQuadratic) -> int:
        a = left.coeffs[0] - right.coeffs[0]
        c = left.coeffs[2] - right.coeffs[2]
        return qsqrt3_sign(a, c)

    return {
        "points": len(points),
        "pairs": len(distances),
        "unit_contacts": contacts,
        "diameter_pairs": diameters,
        "minimum_squared_distance": "1",
        "maximum_squared_distance": format_qsqrt3(upper),
        "diameter": "sqrt(8+4*sqrt(3)) = sqrt(6)+sqrt(2)",
        "squared_distance_classes": [
            {"squared_distance": format_qsqrt3(value), "pairs": classes[value]}
            for value in sorted(classes, key=cmp_to_key(compare))
        ],
    }


def main() -> int:
    try:
        tokens = [int(token) for token in sys.stdin.read().split()]
        print(json.dumps(verify_tokens(tokens), indent=2))
    except (ValueError, ArithmeticError) as exc:
        print(f"certificate rejected: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
