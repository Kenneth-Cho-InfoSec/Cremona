module

public import Erdos103

public section

namespace Erdos103.SlackFlex

noncomputable section

lemma separated_iff_mem_separatedConfigs {n : ℕ} (p : Config n) :
    Separated p ↔ p ∈ separatedConfigs n := by
  constructor
  · intro hp
    unfold separatedConfigs
    simp only [Set.mem_iInter]
    intro i j
    by_cases hij : i = j
    · exact Or.inl hij
    · exact Or.inr (hp i j hij)
  · intro hp
    unfold separatedConfigs at hp
    simp only [Set.mem_iInter] at hp
    intro i j hij
    exact (hp i j).resolve_left hij

def addPoint {n : ℕ} (p : Config n) (x : Point) : Config (n + 1) :=
  Fin.cases x p

def slackBox {n : ℕ} (D : ℝ) : Set (Fin n → ℝ) :=
  {f | ∀ i, 1 < f i ∧ f i < D}

lemma isOpen_slackBox {n : ℕ} (D : ℝ) : IsOpen (slackBox (n := n) D) := by
  rw [isOpen_pi_iff]
  intro f hf
  refine ⟨Finset.univ, fun _ => Set.Ioo (1 : ℝ) D, ?_⟩
  constructor
  · intro i hi
    exact ⟨isOpen_Ioo, Set.mem_Ioo.mpr (hf i)⟩
  · intro g hg i
    exact Set.mem_Ioo.mp ((Set.mem_pi.mp hg) i (by simp))

def distanceVector {n : ℕ} (p : Config n) : Point → Fin n → ℝ :=
  fun y i => dist y (p i)

lemma continuous_distanceVector {n : ℕ} (p : Config n) :
    Continuous (distanceVector p) := by
  apply continuous_pi
  intro i
  change Continuous (fun y : Point => dist y (p i))
  fun_prop

/-- Strict distance slack from every old point persists in a common neighborhood.
This is a finite-product openness argument, with no explicit minimum-margin formula. -/
theorem exists_ball_strict_slack {n : ℕ} (p : Config n) (x : Point) (D : ℝ)
    (hx : ∀ i, 1 < dist x (p i) ∧ dist x (p i) < D) :
    ∃ ε > 0, ∀ y, dist y x < ε →
      ∀ i, 1 < dist y (p i) ∧ dist y (p i) < D := by
  let f := distanceVector p
  have hopen : IsOpen (f ⁻¹' slackBox D) :=
    (isOpen_slackBox D).preimage (continuous_distanceVector p)
  have hxmem : x ∈ f ⁻¹' slackBox D := by
    change f x ∈ slackBox D
    simpa [f, distanceVector, slackBox] using hx
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hopen) x hxmem
  refine ⟨ε, hε, ?_⟩
  intro y hy i
  have hymem : y ∈ f ⁻¹' slackBox D := hball (Metric.mem_ball.mpr (by simpa [dist_comm] using hy))
  change f y ∈ slackBox D at hymem
  exact hymem i

theorem addPoint_separated {n : ℕ} (p : Config n) (x : Point)
    (hp : ∀ i j, i ≠ j → 1 ≤ dist (p i) (p j))
    (hx : ∀ i, 1 < dist x (p i)) :
    ∀ i j, i ≠ j → 1 ≤ dist (addPoint p x i) (addPoint p x j) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp_all
    | succ j =>
      simpa [addPoint] using (le_of_lt (hx j))
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simpa [addPoint, dist_comm] using (le_of_lt (hx i))
    | succ j =>
      apply hp i j
      intro heq
      apply hij
      exact congrArg Fin.succ heq

theorem exists_ball_addPoint_separated {n : ℕ} (p : Config n) (x : Point) (D : ℝ)
    (hp : Separated p)
    (hx : ∀ i, 1 < dist x (p i) ∧ dist x (p i) < D) :
    ∃ ε > 0, ∀ y, dist y x < ε →
      ∀ i j, i ≠ j → 1 ≤ dist (addPoint p y i) (addPoint p y j) := by
  obtain ⟨ε, hε, hslack⟩ := exists_ball_strict_slack p x D hx
  refine ⟨ε, hε, ?_⟩
  intro y hy
  exact addPoint_separated p y hp (fun i => (hslack y hy i).1)

lemma dist_le_diameter {n : ℕ} (hn : 0 < n) (p : Config n) (i j : Fin n) :
    dist (p i) (p j) ≤ diameter hn p := by
  unfold diameter
  exact Finset.le_sup' (s := Finset.univ.product Finset.univ)
    (f := fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2)) (b := (i, j)) (by simp)

lemma diameter_succ_le {n : ℕ} (hn : 0 < n) (q : Config (n + 1)) :
    diameter hn (fun i => q i.succ) ≤ diameter (Nat.succ_pos n) q := by
  have hpairs : (Finset.univ.product Finset.univ : Finset (Fin n × Fin n)).Nonempty := by
    obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hn
    exact ⟨(i, i), by simp⟩
  unfold diameter
  apply Finset.sup'_le hpairs
  intro ij hij
  rcases ij with ⟨i, j⟩
  exact dist_le_diameter (Nat.succ_pos n) q i.succ j.succ

theorem diameter_le_succ_competitor_of_optimal {n : ℕ} (hn : 0 < n)
    (p : Config n) (hp : IsOptimal hn p) (q : Config (n + 1))
    (hq : q ∈ separatedConfigs (n + 1)) :
    diameter hn p ≤ diameter (Nat.succ_pos n) q := by
  have hqsep : Separated q := (separated_iff_mem_separatedConfigs q).2 hq
  let qtail : Config n := fun i => q i.succ
  have hqtail : Separated qtail := by
    intro i j hij
    apply hqsep i.succ j.succ
    intro heq
    apply hij
    apply Fin.ext
    simpa using congrArg Fin.val heq
  have hqtail_min := hp.2 qtail ((separated_iff_mem_separatedConfigs qtail).1 hqtail)
  calc
    diameter hn p ≤ diameter hn qtail := hqtail_min
    _ ≤ diameter (Nat.succ_pos n) q := diameter_succ_le hn q

theorem diameter_addPoint_eq {n : ℕ} (hn : 0 < n) (p : Config n) (x : Point) (D : ℝ)
    (hD : diameter hn p = D) (hD_nonneg : 0 ≤ D)
    (hx : ∀ i, dist x (p i) < D) :
    diameter (Nat.succ_pos n) (addPoint p x) = D := by
  apply le_antisymm
  · unfold diameter
    apply Finset.sup'_le (⟨((0 : Fin (n + 1)), 0), by simp⟩ :
      (Finset.univ.product Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).Nonempty)
    intro ij hij
    rcases ij with ⟨i, j⟩
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simpa [addPoint] using hD_nonneg
      | succ j => simpa [addPoint] using (le_of_lt (hx j))
    | succ i =>
      cases j using Fin.cases with
      | zero => simpa [addPoint, dist_comm] using (le_of_lt (hx i))
      | succ j =>
        calc
          dist (p i) (p j) ≤ diameter hn p := dist_le_diameter hn p i j
          _ = D := hD
  · let pairs : Finset (Fin n × Fin n) := Finset.univ.product Finset.univ
    have hpairs : pairs.Nonempty := by
      obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hn
      exact ⟨(i, i), by simp [pairs]⟩
    obtain ⟨ij, hij, hmax⟩ :=
      Finset.exists_mem_eq_sup' hpairs (fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2))
    have hpair : dist (p ij.1) (p ij.2) = D := by
      have hdiam : diameter hn p = dist (p ij.1) (p ij.2) := by
        simpa [diameter, pairs] using hmax
      rw [hD] at hdiam
      exact hdiam.symm
    calc
      D = dist (p ij.1) (p ij.2) := hpair.symm
      _ = dist (addPoint p x ij.1.succ) (addPoint p x ij.2.succ) := by simp [addPoint]
      _ ≤ diameter (Nat.succ_pos n) (addPoint p x) :=
        dist_le_diameter (Nat.succ_pos n) (addPoint p x) ij.1.succ ij.2.succ

theorem addPoint_isOptimal_of_globalLowerBound {n : ℕ} (hn : 0 < n)
    (p : Config n) (x : Point) (D : ℝ)
    (hp : Separated p) (hD : diameter hn p = D) (hD_nonneg : 0 ≤ D)
    (hx : ∀ i, 1 < dist x (p i) ∧ dist x (p i) < D)
    (hLB : ∀ q, q ∈ separatedConfigs (n + 1) →
      D ≤ diameter (Nat.succ_pos n) q) :
    IsOptimal (Nat.succ_pos n) (addPoint p x) := by
  have hext_sep := addPoint_separated p x hp (fun i => (hx i).1)
  have hext_diam := diameter_addPoint_eq hn p x D hD hD_nonneg (fun i => (hx i).2)
  refine ⟨(separated_iff_mem_separatedConfigs _).1 hext_sep, ?_⟩
  intro q hq
  rw [hext_diam]
  exact hLB q hq

theorem exists_ball_addPoint_isOptimal_of_globalLowerBound {n : ℕ} (hn : 0 < n)
    (p : Config n) (x : Point) (D : ℝ)
    (hp : Separated p) (hD : diameter hn p = D) (hD_nonneg : 0 ≤ D)
    (hx : ∀ i, 1 < dist x (p i) ∧ dist x (p i) < D)
    (hLB : ∀ q, q ∈ separatedConfigs (n + 1) →
      D ≤ diameter (Nat.succ_pos n) q) :
    ∃ ε > 0, ∀ y, dist y x < ε → IsOptimal (Nat.succ_pos n) (addPoint p y) := by
  obtain ⟨ε, hε, hslack⟩ := exists_ball_strict_slack p x D hx
  refine ⟨ε, hε, ?_⟩
  intro y hy
  exact addPoint_isOptimal_of_globalLowerBound hn p y D hp hD hD_nonneg
    (hslack y hy) hLB

theorem addPoint_isOptimal {n : ℕ} (hn : 2 ≤ n) (p : Config n) (x : Point)
    (hp : IsOptimal (by omega) p)
    (hx : ∀ i, 1 < dist x (p i) ∧ dist x (p i) < diameter (by omega) p) :
    IsOptimal (by omega) (addPoint p x) := by
  let hpos : 0 < n := by omega
  let hpos' : 0 < n + 1 := by omega
  have hpsep : Separated p :=
    (separated_iff_mem_separatedConfigs p).2 hp.1
  have hDpos : 0 ≤ diameter hpos p := by
    obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hpos
    have hslack := hx i
    linarith
  have hext_sep : Separated (addPoint p x) :=
    addPoint_separated p x hpsep (fun i => (hx i).1)
  have hext_diam : diameter hpos' (addPoint p x) = diameter hpos p :=
    diameter_addPoint_eq hpos p x (diameter hpos p) rfl hDpos (fun i => (hx i).2)
  refine ⟨(separated_iff_mem_separatedConfigs _).1 hext_sep, ?_⟩
  intro q hq
  have hqsep : Separated q := (separated_iff_mem_separatedConfigs q).2 hq
  let qtail : Config n := fun i => q i.succ
  have hqtail : Separated qtail := by
    intro i j hij
    apply hqsep i.succ j.succ
    intro heq
    apply hij
    apply Fin.ext
    simpa using congrArg Fin.val heq
  have hqtail_min := hp.2 qtail ((separated_iff_mem_separatedConfigs qtail).1 hqtail)
  calc
    diameter hpos' (addPoint p x) = diameter hpos p := hext_diam
    _ ≤ diameter hpos qtail := hqtail_min
    _ ≤ diameter hpos' q := diameter_succ_le hpos q

theorem exists_ball_addPoint_isOptimal {n : ℕ} (hn : 2 ≤ n) (p : Config n) (x : Point)
    (hp : IsOptimal (by omega) p)
    (hx : ∀ i, 1 < dist x (p i) ∧ dist x (p i) < diameter (by omega) p) :
    ∃ ε > 0, ∀ y, dist y x < ε → IsOptimal (by omega) (addPoint p y) := by
  obtain ⟨ε, hε, hslack⟩ := exists_ball_strict_slack p x (diameter (by omega) p) hx
  refine ⟨ε, hε, ?_⟩
  intro y hy
  exact addPoint_isOptimal hn p y hp (hslack y hy)

lemma pairEnergy_addPoint {n : ℕ} (p : Config n) (x : Point) :
    pairEnergy (addPoint p x) = pairEnergy p +
      2 * ∑ i : Fin n, (dist x (p i)) ^ 2 := by
  simp [pairEnergy, addPoint, Fin.sum_univ_succ, dist_comm]
  rw [Finset.sum_add_distrib]
  ring

lemma norm_sq_add_smul (a u : Point) (t : ℝ) :
    ‖a + t • u‖ ^ 2 = ‖a‖ ^ 2 + 2 * t * inner ℝ a u + t ^ 2 * ‖u‖ ^ 2 := by
  calc
    ‖a + t • u‖ ^ 2 = inner ℝ (a + t • u) (a + t • u) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ a a + 2 * t * inner ℝ a u + t ^ 2 * inner ℝ u u := by
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm u a]
      ring
    _ = ‖a‖ ^ 2 + 2 * t * inner ℝ a u + t ^ 2 * ‖u‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

lemma dist_sq_move (x p u : Point) (t : ℝ) :
    (dist (x + t • u) p) ^ 2 = (dist x p) ^ 2 +
      2 * t * inner ℝ (x - p) u + t ^ 2 * ‖u‖ ^ 2 := by
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : x + t • u - p = (x - p) + t • u := by abel
  rw [hsub, norm_sq_add_smul]

lemma sum_dist_sq_move {n : ℕ} (p : Config n) (x u : Point) (t : ℝ) :
    (∑ i : Fin n, (dist (x + t • u) (p i)) ^ 2) =
      (∑ i : Fin n, (dist x (p i)) ^ 2) +
        2 * t * ∑ i : Fin n, inner ℝ (x - p i) u +
        (n : ℝ) * t ^ 2 * ‖u‖ ^ 2 := by
  simp_rw [dist_sq_move]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem pairEnergy_addPoint_motion {n : ℕ} (p : Config n) (x u : Point) (t : ℝ) :
    pairEnergy (addPoint p (x + t • u)) =
      pairEnergy (addPoint p x) +
        4 * t * ∑ i : Fin n, inner ℝ (x - p i) u +
        2 * (n : ℝ) * t ^ 2 * ‖u‖ ^ 2 := by
  calc
    pairEnergy (addPoint p (x + t • u)) =
        pairEnergy p + 2 * ∑ i : Fin n, (dist (x + t • u) (p i)) ^ 2 :=
      pairEnergy_addPoint p (x + t • u)
    _ = (pairEnergy p + 2 * ∑ i : Fin n, (dist x (p i)) ^ 2) +
        4 * t * ∑ i : Fin n, inner ℝ (x - p i) u +
        2 * (n : ℝ) * t ^ 2 * ‖u‖ ^ 2 := by rw [sum_dist_sq_move]; ring
    _ = pairEnergy (addPoint p x) +
        4 * t * ∑ i : Fin n, inner ℝ (x - p i) u +
        2 * (n : ℝ) * t ^ 2 * ‖u‖ ^ 2 := by rw [pairEnergy_addPoint]

def directionalSlope {n : ℕ} (p : Config n) (x u : Point) : ℝ :=
  ∑ i : Fin n, inner ℝ (x - p i) u

def slackDirection {n : ℕ} (p : Config n) (x : Point) : Point :=
  if 0 ≤ directionalSlope p x axis then axis else -axis

lemma directionalSlope_slackDirection_nonneg {n : ℕ} (p : Config n) (x : Point) :
    0 ≤ directionalSlope p x (slackDirection p x) := by
  dsimp [slackDirection]
  split_ifs with h
  · exact h
  · have hneg : directionalSlope p x axis < 0 := lt_of_not_ge h
    have hsum : directionalSlope p x (-axis) = -directionalSlope p x axis := by
      simp [directionalSlope, Finset.sum_neg_distrib]
    rw [hsum]
    linarith

lemma norm_slackDirection {n : ℕ} (p : Config n) (x : Point) :
    ‖slackDirection p x‖ = 1 := by
  dsimp [slackDirection]
  split_ifs
  · exact norm_axis
  · simpa only [norm_neg] using norm_axis

lemma quadratic_energy_strict_mono {n : ℕ} (hn : 0 < n) {A s t : ℝ}
    (hA : 0 ≤ A) (hs : 0 ≤ s) (hst : s < t) :
    4 * s * A + 2 * (n : ℝ) * s ^ 2 < 4 * t * A + 2 * (n : ℝ) * t ^ 2 := by
  have ht : 0 < t := lt_of_le_of_lt hs hst
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : 0 < s + t := by linarith
  have hbracket : 0 < 4 * A + 2 * (n : ℝ) * (s + t) := by positivity
  have hfactor : (4 * t * A + 2 * (n : ℝ) * t ^ 2) -
      (4 * s * A + 2 * (n : ℝ) * s ^ 2) =
        (t - s) * (4 * A + 2 * (n : ℝ) * (s + t)) := by ring
  have hpos : 0 < (t - s) * (4 * A + 2 * (n : ℝ) * (s + t)) :=
    mul_pos (sub_pos.mpr hst) hbracket
  have hdiff : 0 < (4 * t * A + 2 * (n : ℝ) * t ^ 2) -
      (4 * s * A + 2 * (n : ℝ) * s ^ 2) := by rw [hfactor]; exact hpos
  exact (sub_pos.mp hdiff)

theorem pairEnergy_addPoint_motion_strict {n : ℕ} (hn : 0 < n)
    (p : Config n) (x u : Point)
    (hA : 0 ≤ directionalSlope p x u) (hu : ‖u‖ = 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    pairEnergy (addPoint p (x + s • u)) < pairEnergy (addPoint p (x + t • u)) := by
  rw [pairEnergy_addPoint_motion p x u s, pairEnergy_addPoint_motion p x u t, hu]
  simp only [one_pow, mul_one]
  have hquad := quadratic_energy_strict_mono hn hA hs hst
  have hquad' :
      4 * s * (∑ i : Fin n, inner ℝ (x - p i) u) + 2 * (n : ℝ) * s ^ 2 <
      4 * t * (∑ i : Fin n, inner ℝ (x - p i) u) + 2 * (n : ℝ) * t ^ 2 := by
    simpa [directionalSlope] using hquad
  linarith

def slackParameter {k : ℕ} (ε : ℝ) (i : Fin k) : ℝ :=
  ε * (((i.val + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))

lemma slackParameter_pos {k : ℕ} (ε : ℝ) (hε : 0 < ε) (i : Fin k) :
    0 < slackParameter ε i := by
  have hi : 0 < (((i.val + 1 : ℕ) : ℝ)) := by positivity
  have hk : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  unfold slackParameter
  exact mul_pos hε (div_pos hi hk)

lemma slackParameter_lt_eps {k : ℕ} (ε : ℝ) (hε : 0 < ε) (i : Fin k) :
    slackParameter ε i < ε := by
  have hnum : (((i.val + 1 : ℕ) : ℝ)) < (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.add_lt_add_right i.isLt 1
  have hden : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hratio : (((i.val + 1 : ℕ) : ℝ)) / (((k + 1 : ℕ) : ℝ)) < 1 :=
    (div_lt_one hden).2 hnum
  unfold slackParameter
  calc
    ε * ((((i.val + 1 : ℕ) : ℝ)) / (((k + 1 : ℕ) : ℝ))) < ε * 1 :=
      mul_lt_mul_of_pos_left hratio hε
    _ = ε := by ring

lemma slackParameter_lt {k : ℕ} (ε : ℝ) (hε : 0 < ε) {i j : Fin k}
    (hij : i.val < j.val) : slackParameter ε i < slackParameter ε j := by
  have hnum : (((i.val + 1 : ℕ) : ℝ)) < (((j.val + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.add_lt_add_right hij 1
  have hden : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hscale : 0 < ε / (((k + 1 : ℕ) : ℝ)) := div_pos hε hden
  have hi : slackParameter ε i =
      (ε / (((k + 1 : ℕ) : ℝ))) * (((i.val + 1 : ℕ) : ℝ)) := by
    unfold slackParameter
    ring
  have hj : slackParameter ε j =
      (ε / (((k + 1 : ℕ) : ℝ))) * (((j.val + 1 : ℕ) : ℝ)) := by
    unfold slackParameter
    ring
  rw [hi, hj]
  exact mul_lt_mul_of_pos_left hnum hscale

def HasKOptimalClasses (n k : ℕ) (hn : 0 < n) : Prop :=
  ∃ f : Fin k → Config n,
    (∀ i, IsOptimal hn (f i)) ∧
    ∀ i j, i ≠ j → ¬ Congruent (f i) (f j)

/-- A strict-slack point gives many optima whenever a global lower bound already
certifies the diameter of the extension. This version does not require the old
configuration itself to be optimal at size n. -/
theorem strictSlack_gives_many_optima_of_globalLowerBound {n : ℕ} (hn : 0 < n)
    (p : Config n) (x : Point) (D : ℝ)
    (hp : Separated p) (hD : diameter hn p = D) (hD_nonneg : 0 ≤ D)
    (hx : ∀ i, 1 < dist x (p i) ∧ dist x (p i) < D)
    (hLB : ∀ q, q ∈ separatedConfigs (n + 1) →
      D ≤ diameter (Nat.succ_pos n) q)
    {k : ℕ} : HasKOptimalClasses (n + 1) k (Nat.succ_pos n) := by
  obtain ⟨ε, hε, hnear⟩ := exists_ball_addPoint_isOptimal_of_globalLowerBound
    hn p x D hp hD hD_nonneg hx hLB
  let u := slackDirection p x
  have hu : ‖u‖ = 1 := norm_slackDirection p x
  have hA : 0 ≤ directionalSlope p x u := directionalSlope_slackDirection_nonneg p x
  let parameters : Fin k → ℝ := fun i => slackParameter ε i
  let family : Fin k → Config (n + 1) := fun i => addPoint p (x + parameters i • u)
  refine ⟨family, ?_, ?_⟩
  · intro i
    apply hnear
    have hti_nonneg : 0 ≤ parameters i := le_of_lt (slackParameter_pos ε hε i)
    have hti_lt : parameters i < ε := slackParameter_lt_eps ε hε i
    rw [show dist (x + parameters i • u) x = parameters i by
      rw [dist_eq_norm, show x + parameters i • u - x = parameters i • u by abel]
      simp [norm_smul, hu, abs_of_nonneg hti_nonneg]]
    exact hti_lt
  · intro i j hij hcongr
    have hval : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have ht : parameters i < parameters j :=
        slackParameter_lt ε hε hlt
      have henergy := pairEnergy_addPoint_motion_strict (by omega) p x u hA hu
        (le_of_lt (slackParameter_pos ε hε i)) ht
      exact (ne_of_lt henergy) (pairEnergy_congruent hcongr)
    · have ht : parameters j < parameters i :=
        slackParameter_lt ε hε hgt
      have henergy := pairEnergy_addPoint_motion_strict (by omega) p x u hA hu
        (le_of_lt (slackParameter_pos ε hε j)) ht
      exact (ne_of_lt henergy) (pairEnergy_congruent hcongr).symm

/-- A strict-slack point in an optimizer yields arbitrarily many distinct optimal
extensions one size larger; pair energy separates their congruence classes. -/
theorem strictSlack_gives_many_optima {n : ℕ} (hn : 2 ≤ n) (p : Config n) (x : Point)
    (hp : IsOptimal (by omega) p)
    (hx : ∀ i, 1 < dist x (p i) ∧ dist x (p i) < diameter (by omega) p)
    {k : ℕ} : HasKOptimalClasses (n + 1) k (Nat.succ_pos n) := by
  obtain ⟨ε, hε, hnear⟩ := exists_ball_addPoint_isOptimal hn p x hp hx
  let u := slackDirection p x
  have hu : ‖u‖ = 1 := norm_slackDirection p x
  have hA : 0 ≤ directionalSlope p x u := directionalSlope_slackDirection_nonneg p x
  let parameters : Fin k → ℝ := fun i => slackParameter ε i
  let family : Fin k → Config (n + 1) := fun i => addPoint p (x + parameters i • u)
  refine ⟨family, ?_, ?_⟩
  · intro i
    apply hnear
    have hti_nonneg : 0 ≤ parameters i := le_of_lt (slackParameter_pos ε hε i)
    have hti_lt : parameters i < ε := slackParameter_lt_eps ε hε i
    rw [show dist (x + parameters i • u) x = parameters i by
      rw [dist_eq_norm, show x + parameters i • u - x = parameters i • u by abel]
      simp [norm_smul, hu, abs_of_nonneg hti_nonneg]]
    exact hti_lt
  · intro i j hij hcongr
    have hval : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have ht : parameters i < parameters j :=
        slackParameter_lt ε hε hlt
      have henergy := pairEnergy_addPoint_motion_strict (by omega) p x u hA hu
        (le_of_lt (slackParameter_pos ε hε i)) ht
      exact (ne_of_lt henergy) (pairEnergy_congruent hcongr)
    · have ht : parameters j < parameters i :=
        slackParameter_lt ε hε hgt
      have henergy := pairEnergy_addPoint_motion_strict (by omega) p x u hA hu
        (le_of_lt (slackParameter_pos ε hε j)) ht
      exact (ne_of_lt henergy) (pairEnergy_congruent hcongr).symm

/-- If an optimal tuple has an index-zero point incident to neither a unit
contact nor a diameter pair, deleting it preserves the diameter and exposes a
strict-slack insertion point. This yields arbitrarily many tuple-level classes. -/
theorem optimal_with_isolated_point_gives_many_classes {n : ℕ} (hn : 2 ≤ n)
    (q : Config (n + 1)) (hq : IsOptimal (by omega) q)
    (hnoUnit : ∀ j : Fin n, dist (q 0) (q j.succ) ≠ 1)
    (hnoDiameter : ∀ j : Fin n,
      dist (q 0) (q j.succ) ≠ diameter (Nat.succ_pos n) q)
    {k : ℕ} : HasKOptimalClasses (n + 1) k (Nat.succ_pos n) := by
  let D := diameter (Nat.succ_pos n) q
  let p : Config n := fun i => q i.succ
  have hqsep : Separated q := (separated_iff_mem_separatedConfigs q).2 hq.1
  have hp : Separated p := by
    intro i j hij
    apply hqsep i.succ j.succ
    intro heq
    apply hij
    apply Fin.ext
    simpa using congrArg Fin.val heq
  have hcontact : ∀ j : Fin n, 1 < dist (q 0) (p j) := by
    intro j
    have hdist := hqsep 0 j.succ (by
      intro h
      have hv := congrArg Fin.val h
      simp at hv)
    rcases lt_or_eq_of_le hdist with hlt | heq
    · exact hlt
    · exact False.elim (hnoUnit j heq.symm)
  have hDpos : 0 < D := by
    let a : Fin (n + 1) := ⟨0, by omega⟩
    let b : Fin (n + 1) := ⟨1, by omega⟩
    have hab : a ≠ b := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [a, b] at hv
    have hsepab := hqsep a b hab
    have hle := dist_le_diameter (Nat.succ_pos n) q a b
    dsimp [D]
    exact lt_of_lt_of_le (by norm_num) (le_trans hsepab hle)
  have hpdiam_le : diameter (by omega : 0 < n) p ≤ D := by
    exact diameter_succ_le (by omega) q
  have htailPair : ∃ i j : Fin n, dist (p i) (p j) = D := by
    let pairs : Finset (Fin (n + 1) × Fin (n + 1)) :=
      Finset.univ.product Finset.univ
    have hpairs : pairs.Nonempty := by
      exact ⟨(0, 0), by simp [pairs]⟩
    obtain ⟨ij, hij, hmax⟩ :=
      Finset.exists_mem_eq_sup' hpairs
        (fun ij : Fin (n + 1) × Fin (n + 1) => dist (q ij.1) (q ij.2))
    have hmaxeq : D = dist (q ij.1) (q ij.2) := by
      simpa [D, diameter, pairs] using hmax
    rcases ij with ⟨i, j⟩
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        have hzero : D = 0 := by simpa using hmaxeq
        exact False.elim ((ne_of_gt hDpos) hzero)
      | succ j =>
        exact False.elim (hnoDiameter j (by simpa [D] using hmaxeq.symm))
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        have heq : dist (q 0) (q i.succ) = D := by
          rw [dist_comm]
          simpa [D] using hmaxeq.symm
        exact False.elim (hnoDiameter i heq)
      | succ j =>
        exact ⟨i, j, by simpa [p, D] using hmaxeq.symm⟩
  have hpdiam_ge : D ≤ diameter (by omega : 0 < n) p := by
    obtain ⟨i, j, hij⟩ := htailPair
    calc
      D = dist (p i) (p j) := hij.symm
      _ ≤ diameter (by omega) p := dist_le_diameter (by omega) p i j
  have hpdiam : diameter (by omega : 0 < n) p = D :=
    le_antisymm hpdiam_le hpdiam_ge
  have hslack : ∀ j : Fin n,
      1 < dist (q 0) (p j) ∧ dist (q 0) (p j) < D := by
    intro j
    refine ⟨hcontact j, ?_⟩
    have hle := dist_le_diameter (Nat.succ_pos n) q 0 j.succ
    rcases lt_or_eq_of_le (show dist (q 0) (q j.succ) ≤ D by simpa [D] using hle)
        with hlt | heq
    · exact hlt
    · exact False.elim (hnoDiameter j heq)
  have hLB : ∀ r, r ∈ separatedConfigs (n + 1) →
      D ≤ diameter (Nat.succ_pos n) r := by
    intro r hr
    exact hq.2 r hr
  exact strictSlack_gives_many_optima_of_globalLowerBound (by omega) p (q 0) D hp
    hpdiam (le_of_lt hDpos) hslack hLB

end

end Erdos103.SlackFlex
