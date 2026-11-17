module

public import Erdos103

public section

namespace Erdos103.FlexCertificate

abbrev Index := Fin 19
abbrev Axial := ℚ × ℚ

def base : Index → Axial := ![
  (0, 0),
  (-2, 0), (-2, 1), (-2, 2),
  (-1, -1), (-1, 0), (-1, 1), (-1, 2),
  (0, -2), (0, -1), (0, 1), (0, 2),
  (1, -2), (1, -1), (1, 0), (1, 1),
  (2, -2), (2, -1), (2, 0)
]

def velocity : Index → Axial := ![
  (0, 0),
  (0, 0), (-1, 1 / 2), (0, 0),
  (-1, -1), (-1 / 2, 1), (1 / 2, 1 / 2), (-1 / 2, 1),
  (0, 0), (-1, 1 / 2), (1, -1 / 2), (0, 0),
  (1 / 2, -1), (-1 / 2, -1 / 2), (1 / 2, -1), (1 / 2, 1 / 2),
  (0, 0), (1, -1 / 2), (0, 0)
]

def subAxial (a b : Axial) : Axial := (a.1 - b.1, a.2 - b.2)

def sqAxial (a : Axial) : ℚ := a.1 ^ 2 + a.1 * a.2 + a.2 ^ 2

def baseSq (i j : Index) : ℚ := sqAxial (subAxial (base i) (base j))

def linear (i j : Index) : ℚ :=
  let d := subAxial (base i) (base j)
  let v := subAxial (velocity i) (velocity j)
  2 * d.1 * v.1 + d.1 * v.2 + d.2 * v.1 + 2 * d.2 * v.2

def quadratic (i j : Index) : ℚ :=
  sqAxial (subAxial (velocity i) (velocity j))

def axialBilinear (a b : Axial) : ℚ :=
  2 * a.1 * b.1 + a.1 * b.2 + a.2 * b.1 + 2 * a.2 * b.2

lemma sqAxial_add_smul (a b : Axial) (t : ℚ) :
    sqAxial (a + t • b) = sqAxial a + t * axialBilinear a b + t ^ 2 * sqAxial b := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  simp [sqAxial, axialBilinear]
  ring

lemma sqAxial_motion (t : ℚ) (i j : Index) :
    sqAxial (subAxial (base i + t • velocity i) (base j + t • velocity j)) =
      baseSq i j + t * linear i j + t ^ 2 * quadratic i j := by
  have hsub : subAxial (base i + t • velocity i) (base j + t • velocity j) =
      subAxial (base i) (base j) + t • subAxial (velocity i) (velocity j) := by
    ext <;> simp [subAxial] <;> ring
  rw [hsub, sqAxial_add_smul]
  simp [baseSq, linear, quadratic, axialBilinear]

noncomputable def embedAxial (a : Axial) : Point :=
  WithLp.toLp 2 ![(a.1 : ℝ) + (a.2 : ℝ) / 2, (a.2 : ℝ) * Real.sqrt 3 / 2]

theorem dist_embedAxial_sq (a b : Axial) :
    (dist (embedAxial a) (embedAxial b)) ^ 2 =
      (sqAxial (subAxial a b) : ℝ) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt]
  · simp [embedAxial, subAxial, sqAxial, Fin.sum_univ_two]
    have hsq : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [hsq]
  · positivity

noncomputable def movingConfig (t : ℚ) : Config 19 :=
  fun i => embedAxial (base i + t • velocity i)

theorem moving_dist_sq (t : ℚ) (i j : Index) :
    (dist (movingConfig t i) (movingConfig t j)) ^ 2 =
      (baseSq i j + t * linear i j + t ^ 2 * quadratic i j : ℝ) := by
  simp only [movingConfig]
  rw [dist_embedAxial_sq, sqAxial_motion]
  norm_cast

lemma one_le_of_sq_ge_one {x : ℝ} (hx : 0 ≤ x) (hone : 1 ≤ x ^ 2) : 1 ≤ x := by
  by_contra h
  have hlt : x < 1 := lt_of_not_ge h
  have hprod : 0 ≤ x * (1 - x) := mul_nonneg hx (sub_nonneg.mpr (le_of_lt hlt))
  nlinarith

lemma le_four_of_sq_le_sixteen {x : ℝ} (hsixteen : x ^ 2 ≤ 16) : x ≤ 4 := by
  by_contra h
  have hlt : 4 < x := lt_of_not_ge h
  have hprod : 0 < (x - 4) * (x + 4) :=
    mul_pos (sub_pos.mpr hlt) (by linarith)
  nlinarith

def errorBound (i j : Index) : ℚ :=
  |linear i j| * (1 / 10) + quadratic i j * (1 / 10) ^ 2

def pairCertificate (i j : Index) : Prop :=
  if baseSq i j = 1 then
    0 ≤ linear i j ∧ errorBound i j ≤ 15
  else if baseSq i j = 16 then
    linear i j = 0 ∧ quadratic i j = 0
  else
    errorBound i j ≤ min (baseSq i j - 1) (16 - baseSq i j)

theorem base_pair_range : ∀ i j, i ≠ j → 1 ≤ baseSq i j ∧ baseSq i j ≤ 16 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [baseSq, subAxial, sqAxial, base] at *

lemma pairCertificate_symm (i j : Index) : pairCertificate i j = pairCertificate j i := by
  have hb : baseSq i j = baseSq j i := by
    simp [baseSq, subAxial, sqAxial]
    ring
  have hl : linear i j = linear j i := by
    simp [linear, subAxial]
    ring
  have hq : quadratic i j = quadratic j i := by
    simp [quadratic, subAxial, sqAxial]
    ring
  simp [pairCertificate, errorBound, hb, hl, hq]

set_option maxHeartbeats 1000000 in
theorem all_pairs_certified_of_lt : ∀ i j, i.val < j.val → pairCertificate i j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [pairCertificate, errorBound, baseSq, linear, quadratic, subAxial, sqAxial,
      base, velocity] at *

theorem all_pairs_certified : ∀ i j, i ≠ j → pairCertificate i j := by
  intro i j hij
  by_cases hlt : i.val < j.val
  · exact all_pairs_certified_of_lt i j hlt
  · have hval : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    have hgt : j.val < i.val := by omega
    rw [pairCertificate_symm]
    exact all_pairs_certified_of_lt j i hgt

lemma sqAxial_nonneg (a : Axial) : 0 ≤ sqAxial a := by
  have h₁ := sq_nonneg (2 * a.1 + a.2)
  have h₂ := sq_nonneg a.2
  unfold sqAxial
  nlinarith

lemma abs_motion_delta_le (t l q : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 10)
    (hq : 0 ≤ q) :
    |t * l + t ^ 2 * q| ≤ |l| * (1 / 10) + q * (1 / 10) ^ 2 := by
  calc
    |t * l + t ^ 2 * q| ≤ |t * l| + |t ^ 2 * q| := abs_add_le _ _
    _ = |t| * |l| + |t ^ 2| * |q| := by rw [abs_mul, abs_mul]
    _ ≤ |l| * (1 / 10) + q * (1 / 10) ^ 2 := by
      rw [abs_of_nonneg ht0, abs_of_nonneg (sq_nonneg t), abs_of_nonneg hq]
      have ht2 : t ^ 2 ≤ (1 / 10) ^ 2 := by
        have h := mul_nonneg ht0 (sub_nonneg.mpr ht1)
        nlinarith
      calc
        t * |l| + t ^ 2 * q ≤ (1 / 10) * |l| + (1 / 10) ^ 2 * q := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right ht1 (abs_nonneg l))
            (mul_le_mul_of_nonneg_right ht2 hq)
        _ = |l| * (1 / 10) + q * (1 / 10) ^ 2 := by ring

theorem moving_axialSq_bounds (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 10)
    (i j : Index) (hij : i ≠ j) :
    1 ≤ sqAxial (subAxial (base i + t • velocity i) (base j + t • velocity j)) ∧
    sqAxial (subAxial (base i + t • velocity i) (base j + t • velocity j)) ≤ 16 := by
  rw [sqAxial_motion]
  let δ := t * linear i j + t ^ 2 * quadratic i j
  have hmove : baseSq i j + t * linear i j + t ^ 2 * quadratic i j = baseSq i j + δ := by
    dsimp [δ]
    ring
  rw [hmove]
  have hbase := base_pair_range i j hij
  have hcert := all_pairs_certified i j hij
  have hq : 0 ≤ quadratic i j := sqAxial_nonneg _
  have hδ : |δ| ≤ errorBound i j := by
    dsimp [δ, errorBound]
    exact abs_motion_delta_le t (linear i j) (quadratic i j) ht0 ht1 hq
  have hδ' := abs_le.mp hδ
  constructor
  · by_cases h₁ : baseSq i j = 1
    · have hc : 0 ≤ linear i j ∧ errorBound i j ≤ 15 := by
        simpa [pairCertificate, h₁] using hcert
      have hlin : 0 ≤ t * linear i j := mul_nonneg ht0 hc.1
      have hquad : 0 ≤ t ^ 2 * quadratic i j := mul_nonneg (sq_nonneg t) hq
      dsimp [δ]
      rw [h₁]
      linarith
    · by_cases h₁₆ : baseSq i j = 16
      · have hc : linear i j = 0 ∧ quadratic i j = 0 := by
          simpa [pairCertificate, h₁, h₁₆] using hcert
        dsimp [δ]
        rw [h₁₆, hc.1, hc.2]
        norm_num
      · have hc : errorBound i j ≤ min (baseSq i j - 1) (16 - baseSq i j) := by
          simpa [pairCertificate, h₁, h₁₆] using hcert
        have hc' : errorBound i j ≤ baseSq i j - 1 := le_trans hc (min_le_left _ _)
        dsimp [δ]
        linarith [hδ'.1]
  · by_cases h₁ : baseSq i j = 1
    · have hc : 0 ≤ linear i j ∧ errorBound i j ≤ 15 := by
        simpa [pairCertificate, h₁] using hcert
      have hlin : 0 ≤ t * linear i j := mul_nonneg ht0 hc.1
      have hquad : 0 ≤ t ^ 2 * quadratic i j := mul_nonneg (sq_nonneg t) hq
      dsimp [δ]
      rw [h₁]
      linarith
    · by_cases h₁₆ : baseSq i j = 16
      · have hc : linear i j = 0 ∧ quadratic i j = 0 := by
          simpa [pairCertificate, h₁, h₁₆] using hcert
        dsimp [δ]
        rw [h₁₆, hc.1, hc.2]
        norm_num
      · have hc : errorBound i j ≤ min (baseSq i j - 1) (16 - baseSq i j) := by
          simpa [pairCertificate, h₁, h₁₆] using hcert
        have hc' : errorBound i j ≤ 16 - baseSq i j := le_trans hc (min_le_right _ _)
        dsimp [δ]
        linarith [hδ'.2]

theorem moving_dist_bounds (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 10)
    (i j : Index) (hij : i ≠ j) :
    1 ≤ (dist (movingConfig t i) (movingConfig t j)) ^ 2 ∧
    (dist (movingConfig t i) (movingConfig t j)) ^ 2 ≤ 16 := by
  rw [moving_dist_sq]
  have h := moving_axialSq_bounds t ht0 ht1 i j hij
  have hlow : 1 ≤ baseSq i j + t * linear i j + t ^ 2 * quadratic i j := by
    rw [← sqAxial_motion]
    exact h.1
  have hhigh : baseSq i j + t * linear i j + t ^ 2 * quadratic i j ≤ 16 := by
    rw [← sqAxial_motion]
    exact h.2
  constructor
  · exact_mod_cast hlow
  · exact_mod_cast hhigh

theorem moving_separated (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 10) :
    movingConfig t ∈ separatedConfigs 19 := by
  simp only [Erdos103.separatedConfigs, Set.mem_iInter, Set.mem_ofPred_eq]
  intro i j
  by_cases hij : i = j
  · exact Or.inl hij
  · exact Or.inr (one_le_of_sq_ge_one (dist_nonneg)
      (moving_dist_bounds t ht0 ht1 i j hij).1)

theorem moving_endpoint_dist (t : ℚ) :
    dist (movingConfig t (1 : Index)) (movingConfig t (18 : Index)) = 4 := by
  have hsq : (dist (movingConfig t (1 : Index)) (movingConfig t (18 : Index))) ^ 2 = 16 := by
    rw [moving_dist_sq]
    norm_num [baseSq, linear, quadratic, subAxial, sqAxial, base, velocity]
  have hdist : 0 ≤ dist (movingConfig t (1 : Index)) (movingConfig t (18 : Index)) := dist_nonneg
  have hfactor :
      (dist (movingConfig t (1 : Index)) (movingConfig t (18 : Index)) - 4) *
        (dist (movingConfig t (1 : Index)) (movingConfig t (18 : Index)) + 4) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.mp hfactor with h | h <;> linarith

theorem moving_diameter (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 10) :
    diameter (by norm_num : 0 < 19) (movingConfig t) = 4 := by
  apply le_antisymm
  · unfold Erdos103.diameter
    apply Finset.sup'_le
    intro ij hij
    by_cases heq : ij.1 = ij.2
    · simp [heq]
    · exact le_four_of_sq_le_sixteen
        (moving_dist_bounds t ht0 ht1 ij.1 ij.2 heq).2
  · unfold Erdos103.diameter
    have hmem : ((1 : Index), (18 : Index)) ∈ Finset.univ.product Finset.univ := by simp
    rw [← moving_endpoint_dist t]
    exact Finset.le_sup' (f := fun ij : Index × Index =>
      dist (movingConfig t ij.1) (movingConfig t ij.2)) hmem

def baseEnergyR : ℝ := ∑ i : Index, ∑ j : Index, (baseSq i j : ℝ)

def linearEnergyR : ℝ := ∑ i : Index, ∑ j : Index, (linear i j : ℝ)

def quadraticEnergyR : ℝ := ∑ i : Index, ∑ j : Index, (quadratic i j : ℝ)

theorem pairEnergy_moving_raw (t : ℚ) :
    pairEnergy (movingConfig t) =
      baseEnergyR + (t : ℝ) * linearEnergyR + (t : ℝ) ^ 2 * quadraticEnergyR := by
  unfold Erdos103.pairEnergy
  simp_rw [moving_dist_sq]
  simp only [baseEnergyR, linearEnergyR, quadraticEnergyR,
    Finset.sum_add_distrib, ← Finset.mul_sum]

set_option maxHeartbeats 1000000 in
theorem linearEnergyR_value : linearEnergyR = 798 := by
  norm_num [linearEnergyR, linear, subAxial, base, velocity, Fin.sum_univ_succ]

set_option maxHeartbeats 1000000 in
theorem quadraticEnergyR_value : quadraticEnergyR = 426 := by
  norm_num [quadraticEnergyR, quadratic, subAxial, sqAxial, velocity, Fin.sum_univ_succ]

theorem pairEnergy_moving_formula (t : ℚ) :
    pairEnergy (movingConfig t) = pairEnergy (movingConfig 0) +
      798 * (t : ℝ) + 426 * (t : ℝ) ^ 2 := by
  rw [pairEnergy_moving_raw t, pairEnergy_moving_raw 0,
    linearEnergyR_value, quadraticEnergyR_value]
  norm_num
  ring

theorem moving_pairEnergy_strictMono {s t : ℚ} (hs : 0 ≤ s) (hst : s < t)
    (ht : t ≤ 1 / 10) :
    pairEnergy (movingConfig s) < pairEnergy (movingConfig t) := by
  rw [pairEnergy_moving_formula s, pairEnergy_moving_formula t]
  have hstR : (s : ℝ) < (t : ℝ) := by exact_mod_cast hst
  have hsR : 0 ≤ (s : ℝ) := by exact_mod_cast hs
  have htR : (t : ℝ) ≤ ((1 : ℚ) / 10 : ℝ) := by exact_mod_cast ht
  norm_num at htR
  have hsum : 0 ≤ (s : ℝ) + (t : ℝ) := by linarith
  have hpositive :
      0 < (798 : ℝ) + 426 * ((s : ℝ) + (t : ℝ)) := by positivity
  have hproduct := mul_pos (sub_pos.mpr hstR) hpositive
  nlinarith

theorem moving_not_congruent {s t : ℚ} (hs : 0 ≤ s) (hst : s < t)
    (ht : t ≤ 1 / 10) : ¬ Congruent (movingConfig s) (movingConfig t) := by
  apply Erdos103.not_congruent_of_pairEnergy_ne
  intro h
  have hstrict := moving_pairEnergy_strictMono hs hst ht
  rw [h] at hstrict
  exact (lt_irrefl _) hstrict

theorem all_velocities_nonzero : ∃ i, velocity i ≠ (0, 0) := by
  refine ⟨2, ?_⟩
  decide

end Erdos103.FlexCertificate
