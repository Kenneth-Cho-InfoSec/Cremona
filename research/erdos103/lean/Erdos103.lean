module

public import Mathlib

public section

noncomputable section

namespace Erdos103

abbrev Point := EuclideanSpace ℝ (Fin 2)
abbrev Config (n : ℕ) := Fin n → Point

@[expose] def Separated {n : ℕ} (p : Config n) : Prop :=
  ∀ i j, i ≠ j → 1 ≤ dist (p i) (p j)

@[expose] def diameter {n : ℕ} (hn : 0 < n) (p : Config n) : ℝ :=
  (Finset.univ.product Finset.univ).sup'
    (by
      obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hn
      exact ⟨(i, i), by simp⟩)
    (fun ij => dist (p ij.1) (p ij.2))

lemma continuous_diameter {n : ℕ} (hn : 0 < n) :
    Continuous (fun p : Config n => diameter hn p) := by
  unfold diameter
  have hpair : (Finset.univ.product Finset.univ : Finset (Fin n × Fin n)).Nonempty := by
    obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hn
    exact ⟨(i, i), by simp⟩
  let f : Fin n × Fin n → Config n → ℝ := fun ij p => dist (p ij.1) (p ij.2)
  have hf : ∀ ij ∈ Finset.univ.product Finset.univ, Continuous (f ij) := by
    intro ij _
    dsimp [f]
    fun_prop
  have h := Continuous.finset_sup'_apply (s := Finset.univ.product Finset.univ) hpair hf
  simpa only [Finset.sup'_apply] using h

def axis : Point := EuclideanSpace.single 0 1

lemma norm_axis : ‖axis‖ = 1 := by
  simp [axis]

lemma dist_axis_smul (a b : ℝ) :
    dist (a • axis) (b • axis) = |a - b| := by
  rw [dist_eq_norm]
  calc
    ‖a • axis - b • axis‖ = ‖(a - b) • axis‖ := by rw [sub_smul]
    _ = ‖a - b‖ * ‖axis‖ := norm_smul _ _
    _ = |a - b| := by simp [norm_axis]

def lineConfig (n : ℕ) : Config n := fun i => (i.val : ℝ) • axis

@[expose] def separatedConfigs (n : ℕ) : Set (Config n) :=
  ⋂ i : Fin n, ⋂ j : Fin n, {p | i = j ∨ 1 ≤ dist (p i) (p j)}

def boundedConfigs (n : ℕ) (R : ℝ) : Set (Config n) :=
  Set.univ.pi (fun _ : Fin n => Metric.closedBall (0 : Point) R)

def normalizedConfigs {n : ℕ} (hn : 0 < n) : Set (Config n) :=
  {p | p ⟨0, hn⟩ = 0}

def compactFeasible {n : ℕ} (hn : 0 < n) (R : ℝ) : Set (Config n) :=
  normalizedConfigs hn ∩ (separatedConfigs n ∩ boundedConfigs n R)

@[expose] def IsOptimal {n : ℕ} (hn : 0 < n) (p : Config n) : Prop :=
  p ∈ separatedConfigs n ∧ ∀ q, q ∈ separatedConfigs n → diameter hn p ≤ diameter hn q

/-- Congruence ignores labels and permits every Euclidean isometry, including reflections. -/
def Congruent {n : ℕ} (p q : Config n) : Prop :=
  ∃ e : Point ≃ᵢ Point, ∃ σ : Equiv.Perm (Fin n), ∀ i, q i = e (p (σ i))

/-- The ordered version of total squared pairwise-distance energy. -/
@[expose] def pairEnergy {n : ℕ} (p : Config n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (dist (p i) (p j)) ^ 2

lemma separated_injective {n : ℕ} {p : Config n} (hp : p ∈ separatedConfigs n) :
    Function.Injective p := by
  unfold separatedConfigs at hp
  simp only [Set.mem_iInter] at hp
  intro i j hij
  by_contra hne
  have hdist : 1 ≤ dist (p i) (p j) := (hp i j).resolve_left hne
  rw [hij] at hdist
  norm_num at hdist

theorem pairEnergy_congruent {n : ℕ} {p q : Config n} (h : Congruent p q) :
    pairEnergy p = pairEnergy q := by
  rcases h with ⟨e, σ, hσ⟩
  have hdist (i j : Fin n) :
      (dist (q i) (q j)) ^ 2 = (dist (p (σ i)) (p (σ j))) ^ 2 := by
    rw [hσ i, hσ j, e.dist_eq]
  change (∑ i : Fin n, ∑ j : Fin n, (dist (p i) (p j)) ^ 2) =
    ∑ i : Fin n, ∑ j : Fin n, (dist (q i) (q j)) ^ 2
  let F : Fin n → Fin n → ℝ := fun i j => (dist (p i) (p j)) ^ 2
  calc
    ∑ i : Fin n, ∑ j : Fin n, F i j =
        ∑ i : Fin n, ∑ j : Fin n, F (σ i) j := by
      symm
      exact Equiv.sum_comp σ (fun i => ∑ j : Fin n, F i j)
    _ = ∑ i : Fin n, ∑ j : Fin n, F (σ i) (σ j) := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      exact Equiv.sum_comp σ (fun j => F (σ i) j)
    _ = ∑ i : Fin n, ∑ j : Fin n, (dist (q i) (q j)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (hdist i j).symm

theorem not_congruent_of_pairEnergy_ne {n : ℕ} {p q : Config n}
    (henergy : pairEnergy p ≠ pairEnergy q) : ¬ Congruent p q := by
  intro hcongr
  exact henergy (pairEnergy_congruent hcongr)

def centerAtZero {n : ℕ} (hn : 0 < n) (p : Config n) : Config n :=
  fun i => p i - p ⟨0, hn⟩

lemma dist_translate (a b c : Point) : dist (a - c) (b - c) = dist a b := by
  rw [dist_eq_norm, dist_eq_norm]
  rw [show (a - c) - (b - c) = a - b by abel]

lemma isClosed_separatedConfigs {n : ℕ} : IsClosed (separatedConfigs n) := by
  unfold separatedConfigs
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  by_cases hij : i = j
  · simp [hij]
  · have hdist : Continuous (fun p : Config n => dist (p i) (p j)) := by fun_prop
    simpa [hij] using (isClosed_le continuous_const hdist)

lemma isClosed_boundedConfigs {n : ℕ} (R : ℝ) : IsClosed (boundedConfigs n R) := by
  unfold boundedConfigs
  rw [show Set.univ.pi (fun _ : Fin n => Metric.closedBall (0 : Point) R) =
      ⋂ i : Fin n, {p : Config n | p i ∈ Metric.closedBall (0 : Point) R} by
    ext p
    simp]
  apply isClosed_iInter
  intro i
  exact Metric.isClosed_closedBall.preimage (continuous_apply i)

lemma isClosed_normalizedConfigs {n : ℕ} (hn : 0 < n) :
    IsClosed (normalizedConfigs hn) := by
  unfold normalizedConfigs
  exact isClosed_eq (continuous_apply (⟨0, hn⟩ : Fin n)) continuous_const

lemma isClosed_compactFeasible {n : ℕ} (hn : 0 < n) (R : ℝ) :
    IsClosed (compactFeasible hn R) := by
  unfold compactFeasible
  exact (isClosed_normalizedConfigs hn).inter
    (isClosed_separatedConfigs.inter (isClosed_boundedConfigs R))

lemma isCompact_compactFeasible {n : ℕ} (hn : 0 < n) (R : ℝ) :
    IsCompact (compactFeasible hn R) := by
  apply (isCompact_univ_pi fun _ : Fin n => isCompact_closedBall (0 : Point) R).of_isClosed_subset
    (isClosed_compactFeasible hn R)
  intro p hp
  exact hp.2.2

lemma separated_lineConfig {n : ℕ} : lineConfig n ∈ separatedConfigs n := by
  unfold separatedConfigs
  simp only [Set.mem_iInter]
  intro i j
  by_cases hij : i = j
  · simp [hij]
  · right
    change 1 ≤ dist ((i.val : ℝ) • axis) ((j.val : ℝ) • axis)
    rw [dist_axis_smul]
    have hval : i.val ≠ j.val := by
      intro heq
      exact hij (Fin.ext heq)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hstep : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hlt
      have hstep' : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hstep
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hstep : j.val + 1 ≤ i.val := Nat.succ_le_of_lt hgt
      have hstep' : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hstep
      rw [abs_of_nonneg (by linarith)]
      linarith

lemma lineConfig_mem_bounded {n : ℕ} :
    lineConfig n ∈ boundedConfigs n (2 * (n : ℝ)) := by
  unfold boundedConfigs
  rw [Set.mem_univ_pi]
  intro i
  rw [Metric.mem_closedBall]
  change dist ((i.val : ℝ) • axis) (0 : Point) ≤ 2 * (n : ℝ)
  have hdist : dist ((i.val : ℝ) • axis) (0 : Point) = (i.val : ℝ) := by
    rw [show (0 : Point) = (0 : ℝ) • axis by simp, dist_axis_smul]
    simp
  rw [hdist]
  have hi : (i.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast i.isLt.le
  nlinarith

lemma centerAtZero_separated {n : ℕ} (hn : 0 < n) (p : Config n)
    (hp : p ∈ separatedConfigs n) : centerAtZero hn p ∈ separatedConfigs n := by
  unfold separatedConfigs at hp ⊢
  simp only [Set.mem_iInter] at hp ⊢
  intro i j
  by_cases hij : i = j
  · simp [hij]
  · right
    change 1 ≤ dist (p i - p ⟨0, hn⟩) (p j - p ⟨0, hn⟩)
    have hdist := dist_translate (p i) (p j) (p ⟨0, hn⟩)
    rw [hdist]
    exact (hp i j).resolve_left hij

lemma centerAtZero_mem_bounded {n : ℕ} (hn : 0 < n) (p : Config n) (R : ℝ)
    (hdiam : diameter hn p ≤ R) : centerAtZero hn p ∈ boundedConfigs n R := by
  unfold boundedConfigs
  rw [Set.mem_univ_pi]
  intro i
  rw [Metric.mem_closedBall]
  change dist (p i - p ⟨0, hn⟩) 0 ≤ R
  have hpair : dist (p i) (p ⟨0, hn⟩) ≤ diameter hn p := by
    unfold diameter
    exact Finset.le_sup' (f := fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2))
      (b := (i, ⟨0, hn⟩)) (by simp)
  calc
    dist (p i - p ⟨0, hn⟩) 0 = dist (p i) (p ⟨0, hn⟩) := by
      simpa using dist_translate (p i) (p ⟨0, hn⟩) (p ⟨0, hn⟩)
    _ ≤ diameter hn p := hpair
    _ ≤ R := hdiam

lemma centerAtZero_mem_normalized {n : ℕ} (hn : 0 < n) (p : Config n) :
    centerAtZero hn p ∈ normalizedConfigs hn := by
  simp [normalizedConfigs, centerAtZero]

lemma centerAtZero_mem_compactFeasible {n : ℕ} (hn : 0 < n) (p : Config n) (R : ℝ)
    (hsep : p ∈ separatedConfigs n) (hdiam : diameter hn p ≤ R) :
    centerAtZero hn p ∈ compactFeasible hn R := by
  exact ⟨centerAtZero_mem_normalized hn p,
    ⟨centerAtZero_separated hn p hsep, centerAtZero_mem_bounded hn p R hdiam⟩⟩

lemma diameter_centerAtZero {n : ℕ} (hn : 0 < n) (p : Config n) :
    diameter hn (centerAtZero hn p) = diameter hn p := by
  unfold diameter
  congr 1
  funext ij
  exact dist_translate (p ij.1) (p ij.2) (p ⟨0, hn⟩)

lemma lineConfig_mem_compactFeasible {n : ℕ} (hn : 0 < n) :
    lineConfig n ∈ compactFeasible hn (2 * (n : ℝ)) := by
  unfold compactFeasible normalizedConfigs
  exact ⟨by simp [lineConfig], separated_lineConfig, lineConfig_mem_bounded⟩

lemma diameter_lineConfig_le {n : ℕ} (hn : 0 < n) :
    diameter hn (lineConfig n) ≤ 2 * (n : ℝ) := by
  unfold diameter
  apply Finset.sup'_le
  intro ij hij
  change dist ((ij.1.val : ℝ) • axis) ((ij.2.val : ℝ) • axis) ≤ 2 * (n : ℝ)
  rw [dist_axis_smul]
  have hi : (ij.1.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast ij.1.isLt.le
  have hj : (ij.2.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast ij.2.isLt.le
  by_cases h : ij.1.val ≤ ij.2.val
  · have h' : (ij.1.val : ℝ) ≤ (ij.2.val : ℝ) := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith [show 0 ≤ (ij.1.val : ℝ) by positivity]
  · have hnat : ij.2.val ≤ ij.1.val := by omega
    have h' : (ij.2.val : ℝ) ≤ (ij.1.val : ℝ) := by exact_mod_cast hnat
    rw [abs_of_nonneg (by linarith)]
    linarith [show 0 ≤ (ij.2.val : ℝ) by positivity]

theorem exists_global_minimizer {n : ℕ} (hn : 2 ≤ n) :
    ∃ p : Config n, IsOptimal (by omega) p := by
  let hpos : 0 < n := by omega
  let R : ℝ := 2 * (n : ℝ)
  let K := compactFeasible hpos R
  have hKcompact : IsCompact K := by
    simpa [K, R] using isCompact_compactFeasible hpos R
  have hKnonempty : K.Nonempty := by
    refine ⟨lineConfig n, ?_⟩
    simpa [K, R] using lineConfig_mem_compactFeasible hpos
  have hcont : Continuous (fun p : Config n => diameter hpos p) :=
    continuous_diameter hpos
  obtain ⟨p, hp, hmin⟩ := hKcompact.exists_isMinOn hKnonempty hcont.continuousOn
  refine ⟨p, ?_⟩
  refine ⟨hp.2.1, ?_⟩
  intro q hq
  by_cases hqdiam : diameter hpos q ≤ R
  · have hqK : centerAtZero hpos q ∈ K := by
      exact centerAtZero_mem_compactFeasible hpos q R hq hqdiam
    have hminq : diameter hpos p ≤ diameter hpos (centerAtZero hpos q) :=
      (isMinOn_iff.mp hmin) _ hqK
    simpa [K, R, diameter_centerAtZero] using hminq
  · have hlineK : lineConfig n ∈ K := by
      simpa [K, R] using lineConfig_mem_compactFeasible hpos
    have hminline : diameter hpos p ≤ diameter hpos (lineConfig n) :=
      (isMinOn_iff.mp hmin) _ hlineK
    have hlinebound : diameter hpos (lineConfig n) ≤ R := by
      simpa [R] using diameter_lineConfig_le hpos
    exact le_trans hminline (le_trans hlinebound (le_of_not_ge hqdiam))

end Erdos103
