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
  congruence relation.

The asymptotic theorem and the strict-slack flex theorem are not yet formalized.
The file does not import the open Erdős 103 formalization or depend on its
`sorry` declarations.

## Pinned toolchain

- Lean: `leanprover/lean4:v4.35.0`
- Mathlib tag: `v4.35.0`
- Mathlib commit: `56a005855ea17e0b0958f73ec801ae140b0a1679` (also recorded in
  `lake-manifest.json`)

From this directory, run:

```sh
lake build
lake env lean Audit.lean
```

The audit prints the axioms used by the two partial theorems. The standard
Lean/Mathlib foundations may appear; there are no project axioms, `sorry`, or
`admit` in `Erdos103.lean`.
