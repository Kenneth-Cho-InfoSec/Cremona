# Erdős Problem 103 Research Checkpoint

**Date:** 2026-11-16
**Goal state:** In progress; no proof or disproof of h(n)\to\infty.
**Repository:** `Kenneth-Cho-InfoSec/Cremona`, branch `main`, baseline commit `296eaa1540b2aa8c34983a46d6c2f5b155865f24`.
**Research design:** [2026-11-16 design](../../docs/superpowers/specs/2026-11-16-erdos103-research-design.md).

## Exact target

For each n\ge2, a feasible configuration is an n-point subset of \mathbb{R}^2 with every distinct pair at distance at least 1. Its diameter is the largest pairwise distance. An optimizer has minimum diameter among all feasible n-point sets. Congruence allows any Euclidean isometry, including reflection, and ignores point labels.

The positive claim is

\forall k\ge1,\ \exists N\ge2,\ \forall n\ge N,\ h(n)\ge k.

The exact negation is that some fixed k satisfies h(n)<k for arbitrarily large n. Showing h(n)\ge k for infinitely many n is not enough for the positive claim.

## Literature and formalization status

- Erdős Problem 103 is still listed as open. The public record says even h(n)\ge2 for all sufficiently large n is unknown.
- Bateman–Erdős (1951), Theorem 3: D(7)=2, attained only by a regular unit hexagon and its center. Thus h(7)=1. This falsifies a blanket claim that every optimum has a noncongruent flex; it does not bear on the eventual quantifier.
- Bezdek–Fodor (1999) determine D(8). A later published account describes the optimal family as a regular unit heptagon plus one interior point at distance at least 1 from each heptagon vertex. The resulting family has h(8)=infinity by the argument below. The global D(8) lower bound is a literature input and has not been formalized here.
- `google-deepmind/formal-conjectures`, `FormalConjectures/ErdosProblems/103.lean`, already defines separated finite sets, minimizers, Euclidean-isometry congruence, and h(n) in \mathbb{N}\infty. Its limit statement and eventual h(n)\ge2 variant currently have `sorry`; no proof formalization was found in that source.
- Two public we-solve drafts (A1, 2026-09-23; A2, 2026-01-17) are unreviewed and not Lean-checked. A1 already states a strict-slack-point criterion. Treat both as idea records, not established theorems.

## Lean status

The independent package in [lean/](lean/) is pinned to Lean 4.35.0 and Mathlib v4.35.0, with the Mathlib commit fixed in `lake-manifest.json`. Its source defines labeled planar configurations `Fin n -> EuclideanSpace R (Fin 2)`, separation, a finite-sup diameter, global optimality against every separated tuple, and congruence as a permutation followed by a Euclidean isometry. Separation is proved to imply injectivity.

Lean verifies `exists_global_minimizer`: for every n>=2 there is a globally optimal separated n-tuple. The proof normalizes the first point by translation, restricts all points to a closed ball of radius 2n, proves that normalized feasible set compact, and applies the compact continuous-minimum theorem. A collinear tuple supplies nonemptiness and an upper diameter bound; any unnormalized competitor with diameter at most 2n translates into the compact set, while a larger competitor loses to the collinear tuple. Lean also verifies that ordered total squared pairwise-distance energy is invariant under the encoded congruence relation. `Audit.lean` prints only the standard foundations `propext`, `Classical.choice`, and `Quot.sound` for both results.

This is a labeled-tuple representation of n-point sets; the explicit bridge from an injective tuple's range to an n-element `Finset` and the definition of h(n) are still outstanding. No asymptotic statement is formalized. Build and audit from the package directory with `lake build` and `lake env lean Audit.lean`.

## Verified and proposed mathematical facts

### Strict-slack flex lemma (paper proof; not Lean-checked)

Let S be a finite 1-separated set with at least two points, and suppose its diameter is D. Let x be a point outside S such that 1 < |x-p| < D for every p in S. Then there is an epsilon>0 such that every y with |y-x|<epsilon still satisfies 1 < |y-p| < D for all p in S. This follows by taking the minimum of the finitely many positive margins and applying the triangle inequality. Since S already contains a pair at distance D, every S union {y} has diameter D. If D is the global minimum for |S|+1 points, each is optimal.

For E(T)=sum over unordered pairs {a,b} in T of |a-b|^2, E is invariant under every Euclidean isometry. Writing m=|S| and c=(sum of points of S)/m,

sum over p in S of |y-p|^2 = m|y-c|^2 + sum over p in S of |p|^2 - m|c|^2.

Thus along any nonconstant line segment in the open feasible ball, E is a nonconstant quadratic and assumes infinitely many values. Each value gives a distinct congruence class. Hence a single strict-slack point in an optimal configuration proves h(|S|+1)=infinity. The missing asymptotic lemma is to force such a point, or another continuum of optima, for every sufficiently large n. The radius-2 lattice patch below is a feasible counterexample to any claim that arbitrary large-looking feasible packings must contain a point with no unit contacts; it is not known here to be optimal.

### Literature-backed finite-n result: h(8)=infinity

Let S be the seven vertices of the regular unit heptagon, with center c, circumradius R, and diameter D. Here R>1 and D>R. Choose epsilon>0 with epsilon<R-1 and epsilon<D-R. For every unit vector u and every 0<t<epsilon, put x_t=c+tu.

For each p in S, the reverse and forward triangle inequalities give

|x_t-p|\ge R-t>1,\qquad |x_t-p|\le R+t<D.

All old heptagon distances are unchanged and one old pair already has distance D. Therefore S\cup{x_t} is feasible with diameter D. Given the published global result D(8)=D, every such set is optimal.

To distinguish congruence classes, define E(A) as the sum of squared distances over unordered pairs in A. E is invariant under every Euclidean isometry. Since the heptagon vertices sum to 7c,

E(S\cup\{x_t\})=E(S)+\sum_{p\in S}|x_t-p|^2=C+7t^2

for a constant C independent of t. Distinct positive t therefore give incongruent optimal sets, so h(8)=infinity. This elementary flex calculation is not yet Lean-checked, and it does not imply h(n) grows for all sufficiently large n.

### Exact Cremona calibration

The runnable script [hex_lattice.cremona](experiments/hex_lattice.cremona) uses axial coordinates in the triangular-lattice basis e1=(1,0), e2=(1/2,sqrt(3)/2), where squared distance is exactly

d^2=dx^2+dx\,dy+dy^2.

Command: `target/debug/cremona run research/erdos103/experiments/hex_lattice.cremona`
Output: `21`, `12`, `1`, `4`, then degrees `3,3,3,3,3,3,6` (unordered pairs, unit contacts, minimum squared distance, maximum squared distance, and per-point unit-contact degrees). This checks all 21 pairs of the six-point unit hexagon plus its center using exact Int64 arithmetic. Its contact graph is the wheel W7; every point has at least three unit contacts. It is a calibration, not an exhaustive optimizer search or a proof of rigidity under the inequality constraints.

No exact search over candidate configurations has been run, and no nonlinear feasible-flex certificate has been produced. No Lean theorem has been checked yet.

### Exact rigidity stress test

The new runnable example [triangular_patch_r2.cremona](experiments/triangular_patch_r2.cremona) generates the 19-point radius-2 triangular-lattice patch from the axial-coordinate condition max(|q|,|r|,|q+r|)<=2. Exact Cremona output gives 171 unordered pairs, 42 unit contacts, minimum squared distance 1, maximum squared distance 16, and degree histogram 6 vertices of degree 3, 6 of degree 4, and 7 of degree 6. Thus this patch has no strict-slack point.

The reusable exact-rational helper [rigidity_rank.py](tools/rigidity_rank.py) consumes the Cremona output and computes rank 35 for the 42-row rigidity matrix. Since 2n-3=35, the kernel consists only of the three infinitesimal Euclidean motions. This is an equality-constraint calculation: it does not rule out a feasible motion that opens some contacts, and the patch has not been proved globally optimal. Regression tests cover a rigid triangle, a one-flex square cycle, and this patch. The successful commands are:

`python3 research/erdos103/tools/test_rigidity_rank.py`

`target/debug/cremona run research/erdos103/experiments/triangular_patch_r2.cremona | python3 research/erdos103/tools/rigidity_rank.py`

The second command reports `points=19 unit_contacts=42 exact_rank=35 kernel=3`. The helper uses only Python's standard-library `fractions.Fraction`; SciPy is not installed and no floating LP was substituted.

## Independent lines and current falsifiers

1. **Flexible optima (lead):** find an optimal configuration with a genuine feasible motion at fixed minimum diameter. The n=8 family validates the mechanism; the unique n=7 optimizer falsifies any all-n version. Next target: a theorem forcing at least one integrable flex for every sufficiently large n, or a verified optimizer with all points pinned that rules out the proposed sufficient condition.
2. **Boundary-equivalent switches:** find two fillings with the same boundary constraints and prove both preserve the global minimum. No gadget has been identified. Exact cell enumeration or a lower-diameter replacement would falsify a candidate.
3. **Rigidity / bounded multiplicity:** for a disproof, find fixed k and unbounded n_j with h(n_j)<k. No such sequence or classification is known. A second certified optimum at a proposed n_j falsifies a uniqueness claim.

## Prior hypotheses revised

- “Every optimum flexes” is false at n=7 by Bateman–Erdős uniqueness.
- Contact-matrix rank deficiency alone would not prove a feasible motion; it only gives an infinitesimal candidate and may have a second-order obstruction.
- A strict-slack-point criterion is already present in the unreviewed A1 draft. The current refinement is to use total squared-distance energy as a simpler isometry invariant for distinguishing a radial family.
- The finite result h(8)=infinity and the asymptotic statement are logically separate. The key gap is propagation to every large n, not producing a single flexible optimizer.

## Baseline, tools, and repository state

- Authenticated GitHub account: `Kenneth-Cho-InfoSec`. Origin is `https://github.com/Kenneth-Cho-InfoSec/Cremona.git`. Existing tags: v0.1.0 through v0.5.0. No PR, commit, or release has been created for this project yet.
- Graphify generated a local code graph with 1,284 nodes. Its `graphify-out/` directory is currently untracked. The graph query identified the Rust workspace, CI commands, integer arithmetic, and fixture entry points before source inspection.
- The root environment has Lean 4.36.0 and Lake 5.0.0-src. Rust project channel is `stable`; active rustc/cargo are 1.100.0. The cargo and Clippy components were listed as installed but their shims failed; removing and reinstalling those components restored them.
- The research package separately pins Lean/Mathlib 4.35.0; `lake build` succeeds and the axiom audit is recorded above.
- `cargo test --workspace`: PASS, 246/246 tests.
- `cargo build --workspace`: PASS.
- `cargo fmt --all --check`: FAIL on existing formatting differences in `crates/cremona_cli/src/main.rs`, `crates/cremona_core/src/parser.rs`, and `crates/cremona_core/src/sema.rs`.
- `cargo clippy --workspace --all-targets -- -D warnings`: FAIL on existing `needless_range_loop` at `crates/cremona_core/src/sema.rs:276`.
- `target/debug/cremona test cremona-tests --jobs 8`: FAIL, 430/432. `parquet_roundtrip.cremona` reports 318 vs expected 317; `parquet_roundtrip_factor.cremona` reports 188 vs expected 187, after running the fixture generator.
- `target/debug/cremona test --doc`: FAIL, 16/17. README fences pass; `examples/parquet_write.cremona` reports 388 vs expected 387.
- `python3 scripts/fuzz_binary_formats.py`: PASS, 266 cases.
- Fixture and doc runners share a staging area; run them sequentially. Their first concurrent run produced staging errors, which disappeared on the sequential docs rerun.
- No code or fixture files were changed by the baseline runs. Current project changes are the research design, this checkpoint, the experiment script, and generated untracked Graphify output.

## Next obligations

1. Pin Mathlib and create a self-contained Lean package that defines the original objects without importing the open theorem's `sorry`.
2. Prove minimizer existence for every n\ge2 using translation normalization, a collinear n-point upper-bound witness, and compactness of a closed bounded subset of (\mathbb{R}^2)^n.
3. Prove the total squared-distance energy is invariant under isometries and establish the movable-point criterion for unlabeled finite sets.
4. Encode the exact 8-point family and make the D(8) literature input explicit; later formalize its global lower bound if feasible.
5. Extend the triangular-lattice experiment to radii 3 and 4 and compare their exact contact ranks. Then test the inequality tangent cone, including active diameter constraints; a rank-35 equality matrix alone does not settle local jamming.
6. Return to the original eventual quantifier after the finite-n and compactness lemmas; do not treat h(8)=infinity or a subsequence result as completion.
