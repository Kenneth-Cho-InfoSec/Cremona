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
- if a separated `n`-tuple of diameter `D` admits an added point whose
  distances to every old point are strictly between 1 and `D`, and `D` is a
  global lower bound for size `n+1`, then every point in a neighborhood gives
  an optimal `(n+1)`-tuple, with `k` pairwise incongruent extensions for every
  finite `k`; an optimal `n`-tuple supplies the needed lower bound by deletion;
- if an optimal `(n+1)`-tuple has its index-0 point incident to neither a
  unit-distance pair nor a diameter pair, deleting it preserves the diameter
  and gives the strict-slack hypotheses, so the same conclusion follows;
- an explicit 19-point path `movingConfig t`, for rational `0 ≤ t ≤ 1/10`,
  stays 1-separated with diameter exactly 4;
- distinct parameters on that path have different pair energies, so the
  configurations are pairwise incongruent.

The strict-slack result is a conditional one-step propagation theorem, not an
asymptotic theorem: no argument currently supplies a strict-slack point in an
optimal configuration for every sufficiently large size. The diameter-4
19-point path is feasible but not optimal, since a smaller literature
construction is known; it gives no value for `h(19)`. The package does not
import the open Erdős 103 formalization or depend on its `sorry` declarations.
`HasKOptimalClasses` is currently a tuple-level predicate using the package's
permutation-plus-isometry congruence; the bridge to `h(n)` defined on finite
sets remains a separate proof obligation.

## Pinned toolchain

- Lean: `leanprover/lean4:v4.35.0`
- Mathlib tag: `v4.35.0`
- Mathlib commit: `56a005855ea17e0b0958f73ec801ae140b0a1679` (also recorded in
  `lake-manifest.json`)

From this directory, run:

```sh
lake build
lake build Erdos103.FlexCertificate
lake build Erdos103.SlackFlex
lake env lean Audit.lean
```

The audit prints the axioms used by the minimizer, congruence, flex,
strict-slack, and isolated-point theorems. They use only Lean/Mathlib foundations (`propext`,
`Classical.choice`, and `Quot.sound`). The Lean sources contain no project
axioms, `sorry`, or `admit`.
