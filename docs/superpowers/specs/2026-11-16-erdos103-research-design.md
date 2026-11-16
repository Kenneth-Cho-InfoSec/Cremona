# Erdős Problem 103 Research Design

**Date:** 2026-11-16
**State:** First research tranche; the original problem remains open.
**Goal:** Prove or disprove that the number h(n) of congruence classes of diameter-minimizing unit-separated n-point sets in the plane tends to infinity, and verify the final result in Lean 4.

## Intent and scope

This project will pursue the exact statement

\forall k\ge 1,\ \exists N\ge 2,\ \forall n\ge N,\ h(n)\ge k,

or its exact negation: some fixed k has h(n)<k for arbitrarily large n. The points are unlabeled, feasibility means pairwise Euclidean distance at least 1, and congruence includes translations, rotations, and reflections.

The first tranche leads with flexible optima, as selected in the conversation. It will formalize compactness and a movable-point criterion, then apply that criterion to the known 8-point optimizer. This is a finite-n checkpoint, not a proposed resolution of the limit. A durable checkpoint will record which claims are proved in Lean, which are literature inputs, search bounds, failures, repository revisions, and the next experiment.

## Goals

- Define finite planar configurations, feasibility, diameter, global optimality, and Euclidean congruence in Lean, with quantifiers matching the problem statement.
- Prove a minimizer exists for every n\ge2 by translating a minimizing sequence into a bounded region and using compactness.
- Formalize a sufficient condition for infinitely many incongruent optima: an optimal configuration has a point that can move in an open region while every pairwise separation and the diameter bound remain valid.
- Use the isometry-invariant total squared-distance energy to distinguish a radial family of such configurations. For a fixed finite set S with centroid c, the energy contribution from x=c+tu is a constant plus |S|t^2.
- Apply the criterion to the regular-heptagon-plus-interior-point family for n=8, keeping the published D(8) lower bound separate from the new flex calculation.
- Use Cremona to generate exact triangular-lattice contact data. Its current Int64 arithmetic suffices for bounded lattice experiments; add a reusable compiler or library capability only if a concrete experiment is blocked.
- Continue the local-switch and bounded-multiplicity rigidity tracks independently after the flex checkpoint.

## Non-goals and constraints

- No claim that h(n)\to\infty follows from h(8)=\infty or from a subsequence result.
- No numerical floating-point result will count as a feasibility or optimality proof.
- No use of a Lean theorem with `sorry`, `admit`, or a custom axiom in the final proof dependency closure. The existing Formal Conjectures statement for Erdős 103 is a reference for definitions, not an imported trust boundary.
- No change to Cremona's core language or public standard library unless a specified experiment cannot be done with the existing language and exact bounded integer arithmetic.
- No release is planned for a research note or one-off experiment. A release requires a reusable Cremona improvement and the repository's release checks.

## Approaches

1. **Flexible optima — selected lead.** Search for strict slack or an integrable feasible motion at fixed optimal diameter. A valid motion gives many coordinate configurations; an isometry-invariant energy or distance invariant must then distinguish congruence classes. A rigid optimizer or a second-order obstruction falsifies a proposed motion. The known unique 7-point optimizer is a counterexample to the overstrong claim that every optimum flexes.
2. **Boundary-equivalent switching gadgets.** Find two noncongruent fillings of a region with identical boundary interactions, then prove replacements preserve the global optimum. Failure to find a pair by exact finite enumeration, or a lower-diameter competitor after replacement, falsifies a proposed gadget. The asymptotic proof must work for every sufficiently large n, not just an infinite subsequence.
3. **Rigidity and bounded multiplicity.** To disprove the limit, seek a fixed k and an unbounded sequence n_j with h(n_j)<k. A useful lemma would classify every optimizer on such a sequence by a bounded number of rigid contact-graph realizations. A second certified contact pattern or an unclassified realization falsifies a proposed classification.

## Implementation choices

- **Lean:** keep an independent, self-contained Lean package under `research/erdos103/lean/`, pinned to exact Lean and Mathlib revisions. This avoids importing an upstream module that contains the open theorem with `sorry`, while allowing its definitions to serve as a comparison point. The first Lean milestones are existence and the movable-point/energy lemmas; the full asymptotic statement remains the target.
- **Cremona:** keep research examples and any later certificates under `research/erdos103/experiments/`. Start with an exact triangular-lattice calculation using Int64 coordinates and squared distances. A Rust, Python, or Cremona library extension is deferred until the next experiment demonstrates a real missing capability.
- **Repository workflow:** work on a feature branch and use a pull request. CI runs on pushes and pull requests. The current main-branch baseline has pre-existing format, Clippy, fixture, and doc-example failures recorded in the checkpoint; any proposed change must be tested separately from those baseline failures. Existing tags are v0.1.0 through v0.5.0; this tranche does not warrant a release.

## Current evidence and limits

- Bateman and Erdős prove D(7)=2 with a unique optimizer: the regular unit hexagon and its center. This rules out a universal flexibility lemma, but says nothing about all sufficiently large n.
- Bezdek and Fodor determine D(8). A later published account describes the optimal family as a regular unit heptagon with an interior eighth point at distance at least 1 from each vertex. Since the heptagon has strict radial slack at its center, a small open disk of positions preserves feasibility and the hull diameter. The total squared-distance energy varies with the point's radius, so these positions include infinitely many pairwise incongruent optimizers. This derivation is not yet Lean-checked.
- A public, unreviewed 2026 draft already states the strict-slack-point criterion and correctly identifies the asymptotic gap. The energy invariant is the refinement to test and formalize here.
- An exact Cremona experiment on the 7-point triangular-lattice patch computed 12 unit contacts, minimum squared distance 1, and maximum squared distance 4 over all 21 unordered pairs. This is a calibration example, not an optimizer search.
- No candidate lower bound for all feasible configurations beyond published small-n results has been formalized in this tranche.

## Verification and release policy

The repository's current gates are `cargo fmt --all --check`, `cargo clippy --workspace --all-targets -- -D warnings`, `cargo test --workspace`, debug and release fixture suites, and the docs/examples suite. At baseline, 246 Rust tests and 266 binary-mutation cases pass; formatting and Clippy fail on existing warnings; the fixture suite has two Parquet size mismatches; the docs suite has one Parquet size mismatch. Re-run gates serially because the fixture and doc runners share a staging area. Record command output and toolchain versions in each checkpoint.

Lean artifacts will pin `lean-toolchain` and the Mathlib commit, build from a clean checkout, and run `#print axioms` on every named theorem claimed as proved. No release is cut until a reusable Cremona capability is present and all required checks pass.

## Open proof obligations

1. Prove existence of a diameter minimizer for every n\ge2 in Lean.
2. Prove the movable-point criterion and squared-distance energy invariant in Lean, including invariance under all Euclidean isometries and unlabeled point-set congruence.
3. Formalize the exact 8-point geometric family and isolate the cited global lower bound as a separately proved theorem or a clearly stated literature hypothesis until formalized.
4. Find a theorem that propagates slack points or local switches to every sufficiently large n, or abandon the flex route if exact candidates show all optima are jammed.
5. If flexibility fails, pursue boundary switches and the counterexample-side rigidity classification without weakening the original quantifiers.

## References

- P. Bateman and P. Erdős, “Geometrical Extrema Suggested by a Lemma of Besicovitch,” American Mathematical Monthly 58 (1951), 306–314.
- A. Bezdek and F. Fodor, “Minimal Diameter of Certain Sets in the Plane,” Journal of Combinatorial Theory, Series A 85 (1999), 105–111, DOI 10.1006/jcta.1998.2889.
- Formal Conjectures, `FormalConjectures/ErdosProblems/103.lean` (statement and definitions; open theorem remains `sorry`).
- Public unreviewed research drafts: we-solve Math-8071-A1 r1 (2026-09-23) and Math-8071-A2 r1 (2026-01-17); use as leads only, not verified sources.
