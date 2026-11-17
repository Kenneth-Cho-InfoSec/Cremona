# Erdős Problem 103 Research Checkpoint

**Date:** 2026-11-17
**Goal state:** In progress; no proof or disproof of h(n)\to\infty.
**Repository:** `Kenneth-Cho-InfoSec/Cremona`, research branch `research/erdos103-flexibility`, based on `main` at `296eaa1540b2aa8c34983a46d6c2f5b155865f24`. Draft PR #5: https://github.com/Kenneth-Cho-InfoSec/Cremona/pull/5.
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

Lean verifies `exists_global_minimizer`: for every n>=2 there is a globally optimal separated n-tuple. The proof normalizes the first point by translation, restricts all points to a closed ball of radius 2n, proves that normalized feasible set compact, and applies the compact continuous-minimum theorem. A collinear tuple supplies nonemptiness and an upper diameter bound; any unnormalized competitor with diameter at most 2n translates into the compact set, while a larger competitor loses to the collinear tuple. Lean also verifies that ordered total squared pairwise-distance energy is invariant under the encoded congruence relation.

The module `Erdos103.FlexCertificate` now verifies a concrete 19-point path. Axial coordinates (q,r) are embedded in the plane as (q+r/2, sqrt(3)r/2), whose squared distance is q^2+qr+r^2. For every rational t in [0,1/10], the resulting configuration is 1-separated and has diameter exactly 4. Its ordered pair-energy satisfies E(t)=E(0)+798t+426t^2, so distinct parameters give incongruent configurations. The contact-and-diameter inequalities are checked by an exact rational certificate, then transferred to Euclidean distances in Lean. `Audit.lean` prints only `propext`, `Classical.choice`, and `Quot.sound` for the verified minimizer, energy-invariance, flex, and noncongruence theorems; no `native_decide` axiom is used.

This is a labeled-tuple representation of n-point sets; the explicit bridge from an injective tuple's range to an n-element `Finset` and the definition of h(n) are still outstanding. The 19-point path is only feasible, not proved optimal, so it gives no lower bound for h(19). No asymptotic statement is formalized. Build and audit from the package directory with `lake build Erdos103 Erdos103.FlexCertificate` and `lake env lean Audit.lean`.

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

No exact search or lower-bound proof establishing global optimality of a 19-point candidate has been run. The exact one-sided feasible-flex certificate and Lean results are recorded below.

### Exact rigidity stress test

The runnable example [triangular_shells.cremona](experiments/triangular_shells.cremona) generates radius-2, radius-3, and radius-4 triangular-lattice patches in axial coordinates. Its exact outputs are:

| Radius | Points | Unordered pairs | Unit contacts | Max squared distance | Contact degrees (3, 4, 6) | Rigidity rank |
| --- | ---: | ---: | ---: | ---: | --- | ---: |
| 2 | 19 | 171 | 42 | 16 | (6, 6, 7) | 35 |
| 3 | 37 | 666 | 90 | 36 | (6, 12, 19) | 71 |
| 4 | 61 | 1830 | 156 | 64 | (6, 18, 37) | 119 |

Every vertex has at least three unit contacts, so none has strict slack. The reusable exact-rational helper [rigidity_rank.py](tools/rigidity_rank.py) consumes the generated coordinate blocks, independently checks their pair counts, contact counts, squared-distance ranges, and degree histograms, then computes the rigidity-matrix rank. Each rank is 2n-3, so the equality-constraint kernel contains only the three infinitesimal Euclidean motions. This does not rule out feasible motions that open some contacts, and none of these patches is proved globally optimal. Regression tests also cover a rigid triangle and a one-flex square cycle. The successful commands are:

`python3 research/erdos103/tools/test_rigidity_rank.py`

`target/debug/cremona run research/erdos103/experiments/triangular_shells.cremona | python3 research/erdos103/tools/rigidity_rank.py`

The second command reports the three rows in the table. The helper uses only Python's standard-library `fractions.Fraction`; SciPy is not installed and no floating LP was substituted.

## Lean-verified feasible flex (not an optimizer)

The radius-2 patch has a genuine one-sided feasible motion even though its equality-framework rigidity matrix has full rank 2n-3. This was found by solving the rational first-order inequalities for all 42 unit contacts and the 3 diameter pairs, then checked exactly. The velocity vector is recorded in [triangular_patch_r2_flex.json](certificates/triangular_patch_r2_flex.json); the reusable verifier is [flex_certificate.py](tools/flex_certificate.py), with regression tests in `test_rigidity_rank.py`.

For an axial pair $(q,r)$, the planar embedding $(q+r/2,r\sqrt{3}/2)$ has squared distance $q^2+qr+r^2$. Along $p_i(t)=b_i+t v_i$, each squared distance is $d_{ij}^2+tL_{ij}+t^2Q_{ij}$. The certificate verifies $L_{ij}\ge0$ for unit contacts, $L_{ij}=Q_{ij}=0$ at diameter pairs, and exact error bounds for all other pairs over $0\le t\le1/10$. In particular every pair remains in the squared-distance interval $[1,16]$, while fixed diameter pairs remain at 16.

Lean verifies the embedding identity, the full pair certificate, 1-separation, diameter exactly 4, and the ordered pair-energy formula $E(t)=E(0)+798t+426t^2$. By the already proved congruence invariance of pair energy, any two different rational parameters in the interval give incongruent configurations. Thus this is an infinite family of feasible 19-point configurations with fixed diameter 4. **No lower bound proving $D(19)=4$ is known here**, so it does not show that any member is optimal or give information about $h(19)$. The result instead falsifies the inference that full rank of the unit-contact framework alone prevents an inequality-feasible flex.

Commands passed on 2026-11-17:

`python3 research/erdos103/tools/test_rigidity_rank.py` (7 tests)

`python3 research/erdos103/tools/flex_certificate.py research/erdos103/certificates/triangular_patch_r2_flex.json` (19 points, 171 pairs, 42 unit contacts, exact rank 35, diameter squared 16, epsilon 1/10, unordered energy coefficients 399 and 213)

`lake build Erdos103 Erdos103.FlexCertificate && lake env lean Audit.lean`

The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; the finite certificate uses `norm_num`, not `native_decide`. A source scan found no `sorry`, `admit`, or project `axiom` declarations.

## Independent lines and current falsifiers

1. **Flexible optima (lead):** find an optimal configuration with a genuine feasible motion at fixed minimum diameter. The n=8 family validates the mechanism; the unique n=7 optimizer falsifies any all-n version. Next target: a theorem forcing at least one integrable flex for every sufficiently large n, or a verified optimizer with all points pinned that rules out the proposed sufficient condition.
2. **Boundary-equivalent switches:** find two fillings with the same boundary constraints and prove both preserve the global minimum. No gadget has been identified. Exact cell enumeration or a lower-diameter replacement would falsify a candidate.
3. **Rigidity / bounded multiplicity:** for a disproof, find fixed k and unbounded n_j with h(n_j)<k. No such sequence or classification is known. A second certified optimum at a proposed n_j falsifies a uniqueness claim.

## Prior hypotheses revised

- “Every optimum flexes” is false at n=7 by Bateman–Erdős uniqueness.
- Contact-matrix rank deficiency alone would not prove a feasible motion; it only gives an infinitesimal candidate and may have a second-order obstruction. Conversely, full equality-framework rank does not imply inequality jamming: the radius-2 patch has rank 2n-3 and the certified one-sided feasible path above.
- A strict-slack-point criterion is already present in the unreviewed A1 draft. The current refinement is to use total squared-distance energy as a simpler isometry invariant for distinguishing a radial family.
- The finite result h(8)=infinity and the asymptotic statement are logically separate. The key gap is propagation to every large n, not producing a single flexible optimizer.

## Baseline, tools, and repository state

- Authenticated GitHub account: `Kenneth-Cho-InfoSec`. Origin is `https://github.com/Kenneth-Cho-InfoSec/Cremona.git`. Existing tags: v0.1.0 through v0.5.0. Draft PR #5 is open at https://github.com/Kenneth-Cho-InfoSec/Cremona/pull/5 on branch `research/erdos103-flexibility`. The tested flex implementation was published in commit `134fd6df241d922c7f3f88b698cc633cd82727fa` (https://github.com/Kenneth-Cho-InfoSec/Cremona/commit/134fd6df241d922c7f3f88b698cc633cd82727fa); a follow-up checkpoint commit records the PR and toolchain state. The PR includes the exact flex certificate, Lean verification, and regression tests. GitHub reports no branch checks. No release is warranted for this research-only addition.
- Graphify generated a local code graph with 1,317 nodes. Its `graphify-out/` directory is generated and should not be staged. Graphify's code extractor skips Lean files; the Lean package is validated directly with Lake.
- The root environment has Lean 4.36.0 and Lake 5.0.0-src. Rust project channel is `stable`; active rustc/cargo are 1.100.0. The cargo and Clippy components were listed as installed but their shims failed; removing and reinstalling those components restored them.
- The research package separately pins Lean/Mathlib 4.35.0 (Lean commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`). `lake build Erdos103 Erdos103.FlexCertificate` and the axiom audit pass. No project `sorry`, `admit`, or custom `axiom` appears in the package; all flex-theorem audits list only `propext`, `Classical.choice`, and `Quot.sound`.
- `cargo test --workspace`: PASS, 246/246 tests.
- `cargo build --workspace`: PASS.
- `cargo fmt --all --check`: FAIL on existing formatting differences in `crates/cremona_cli/src/main.rs`, `crates/cremona_core/src/parser.rs`, and `crates/cremona_core/src/sema.rs`.
- `cargo clippy --workspace --all-targets -- -D warnings`: FAIL on existing `needless_range_loop` at `crates/cremona_core/src/sema.rs:276`.
- `target/debug/cremona test cremona-tests --jobs 8`: FAIL, 430/432. `parquet_roundtrip.cremona` reports 318 vs expected 317; `parquet_roundtrip_factor.cremona` reports 188 vs expected 187, after running the fixture generator.
- `target/debug/cremona test --doc`: FAIL, 16/17. README fences pass; `examples/parquet_write.cremona` reports 388 vs expected 387.
- `python3 scripts/fuzz_binary_formats.py`: PASS, 266 cases.
- Fixture and doc runners share a staging area; run them sequentially. Their first concurrent run produced staging errors, which disappeared on the sequential docs rerun.
- The baseline Rust runs did not change Rust or fixture files. Research changes add exact flex-certificate data and verification, Lean formalization, tests, and checkpoint updates; generated `graphify-out/` remains untracked.

## Next obligations

1. Bridge injective labeled tuples to n-element finite sets, define h(n) with the original unlabeled congruence relation, and formalize the strict-slack-point theorem.
2. Formalize or independently reprove the D(8) lower bound; the literature-backed h(8)=infinity result remains unformalized and does not settle the tail.
3. Search for a global lower bound matching the radius-2 patch's diameter 4, or replace it with a certified optimal candidate. Until then the 19-point flexible family has no bearing on h(19).
4. Continue the switch-gadget and bounded-multiplicity tracks independently; identify an asymptotic construction for every sufficiently large n or a fixed-k bounded-multiplicity subsequence.
5. Return to the exact eventual quantifier, with no finite-n family or subsequence result treated as completion.
