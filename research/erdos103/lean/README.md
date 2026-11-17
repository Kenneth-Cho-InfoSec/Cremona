# Erdős Problem 103 Lean checkpoint

This independent Lean package currently formalizes labeled configurations as
maps `Fin n → EuclideanSpace ℝ (Fin 2)`. Pairwise separation makes each map
injective, so labels can be forgotten by quotienting under permutations.
`Congruent` explicitly allows a permutation and any Euclidean isometry,
including reflections. `IsOptimal` compares the finite maximum distance
against every separated `n`-tuple, with no restriction to a candidate family.

The verified partial results are:

- a globally diameter-minimizing separated configuration exists for every
  `n ≥ 2`;
- total squared pairwise-distance energy is invariant under the defined
  congruence relation;
- an explicit 19-point path `movingConfig t`, for rational `0 ≤ t ≤ 1/10`,
  stays 1-separated with diameter exactly 4;
- distinct parameters on that path have different pair energies, so the
  configurations are pairwise incongruent.

This is a family of feasible configurations, not a family of proven
optimizers: no lower bound showing that diameter 4 is minimal for 19 points is
known here. It therefore gives no value for `h(19)` and does not establish the
asymptotic claim. The package does not import the open Erdős 103 formalization
or depend on its `sorry` declarations.

## Pinned toolchain

- Lean: `leanprover/lean4:v4.35.0`
- Mathlib tag: `v4.35.0`
- Mathlib commit: `56a005855ea17e0b0958f73ec801ae140b0a1679` (also recorded in
  `lake-manifest.json`)

From this directory, run:

```sh
lake build
lake build Erdos103.FlexCertificate
lake env lean Audit.lean
```

The audit prints the axioms used by the minimizer, congruence, and flex
theorems. They use only Lean/Mathlib foundations (`propext`, `Classical.choice`,
and `Quot.sound`). The Lean sources contain no project axioms, `sorry`, or
`admit`.
