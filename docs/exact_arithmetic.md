# Exact arithmetic and geometry libraries

This branch adds exact, pure-Cremona support for computations that must not
depend on floating-point rounding:

| Module | Main types and functions |
|---|---|
| `std.integer` | Checked absolute value, negation, division, remainder, gcd, integer square root, and exponentiation for `Int64` |
| `std.bigint` | Signed arbitrary-precision integers, decimal parsing/formatting, comparison, arithmetic, division/remainder, gcd, floor square root, and square testing |
| `std.rational` | Reduced fractions with positive denominators, exact arithmetic/comparison, and exact-square-root recognition |
| `std.exact_linalg` | Dense row-major rational matrices, transpose, multiplication, determinant, and exact square-system solving |
| `std.algebraic` | Exact arithmetic and sign tests in one quadratic field `Q(sqrt(d))` |
| `std.geometry` | Rational-coordinate points, exact squared distances, separation/diameter checks, and distance-matrix relabeling |
| `std.certificate` | Floor-square-root witnesses and a verifier for closed integer disks' lattice-point counts |

## Integer and rational representations

`BigInt` stores a sign and little-endian base-`10^9` limbs. Limb products,
the output digit, and carry remain below \(10^{18}+2\cdot10^9\), so each
primitive limb operation fits in `Int64`. Long division chooses each quotient
limb by binary search. Division truncates toward zero; a nonzero remainder has
the dividend's sign. `bigint_to_i64` returns `None` when the value does not
fit, including positive \(2^{63}\). `bigint_isqrt_floor` uses integer Newton
iteration and returns `None` for negative inputs.

`Rational` values made by `rational_new` or `rational_from_i64` are reduced,
use a positive denominator, and reject denominator zero. Arithmetic remains
exact; `rational_div` returns `None` for a zero divisor.
`rational_sqrt_exact` returns a value only when the reduced numerator and
denominator are both integer squares. Comparisons cross multiply with
`BigInt`.

The language does not yet support private struct fields. The representation
fields are consequently visible, and direct struct literals can bypass these
invariants. Use the constructors and keep values canonical when constructing
certificates or matrices.

## Linear algebra and algebraic values

`ExactMatrix` owns a flat row-major `Vec<Rational>`. Constructors validate
shape and multiplication overflow. `exact_determinant` uses rational Gaussian
elimination; `exact_solve` returns `None` for nonsquare, mismatched, or
singular systems. No numerical pivot tolerance or approximate conversion is
used.

`QuadraticReal` represents \(a+b\sqrt d\) for rational \(a,b,d\) with
\(d\ge0\). Its exact sign test handles the opposing-sign case by comparing
\(a^2\) with \(b^2d\), so it does not approximate a square root. Addition,
multiplication, division, and ordering require equal radicands. This is a
quadratic-field type, not a representation of arbitrary real algebraic
numbers; operations involving different radicands return `None`. Perfect-
square rational radicands are reduced into the rational part during
construction, so field division keeps a nonzero norm.

## Geometry and certificates

`Point2Rat` uses rational coordinates. Distances are represented first by
their exact rational squared values, which is enough for unit-separation and
diameter comparisons. `distance_exact` returns the corresponding quadratic
real. `distance_matrices_match` checks a supplied bijective relabeling; equal
complete pairwise-distance matrices certify congruence of the finite point
sets.

`verify_root_floor` checks \(r^2\le q<(r+1)^2\) with `BigInt`. A
`DiskRootCertificate` supplies the roots \(\lfloor\sqrt{R^2-x^2}\rfloor\)
for \(0\le x\le R\); the verifier checks every root and the exact identity
\[
  |\mathbb Z^2\cap B(0,R)|=(2R+1)+2\left(r_0+2\sum_{x=1}^R r_x\right).
\]
This verifies a finite counting certificate. It does not establish a
lower bound for all planar packings or global optimality.

## Reproducible examples

The compile-pass fixtures are runnable with the Cremona compiler:

```sh
target/debug/cremona run cremona-tests/compile-pass/exact_arithmetic.cremona
target/debug/cremona run cremona-tests/compile-pass/exact_linalg.cremona
target/debug/cremona run cremona-tests/compile-pass/exact_algebraic.cremona
target/debug/cremona run cremona-tests/compile-pass/exact_geometry.cremona
target/debug/cremona run cremona-tests/compile-pass/exact_certificate.cremona
target/debug/cremona test cremona-tests
```
