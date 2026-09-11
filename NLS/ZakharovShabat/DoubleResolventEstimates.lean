import NLS.ZakharovShabat.DoubleResolvent
import NLS.ZakharovShabat.VerticalStrips
import NLS.SequenceSpaces.ConvolutionSandwich
import NLS.SequenceSpaces.ReciprocalTail

/-!
# The frequency-tail estimate for the double free resolvent

Lemma 3.4 follows by splitting the two reciprocal symbols into windows about
opposite scalar Fourier frequencies. The two far terms decay as `|n|^(-1/p)`;
the near-near term contains only the symmetric potential remainder.
All constants refer to the maximum norm on pairs.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞}

/-- The symmetric remainder in both potential components. -/
def pairFourierTail (N : ℕ) (φ : PairSpace p) : PairSpace p :=
  (Coeff.fourierTail N φ.1, Coeff.fourierTail N φ.2)

@[simp] theorem pairFourierTail_zero (φ : PairSpace p) : pairFourierTail 0 φ = φ := by
  simp [pairFourierTail]

variable [Fact (1 ≤ p)]

local instance : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

theorem norm_pairFourierTail_le (N : ℕ) (φ : PairSpace p) : ‖pairFourierTail N φ‖ ≤ ‖φ‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne'
  exact norm_prod_le_iff.mpr
    ⟨(Coeff.norm_fourierTail_le hp0 N φ.1).trans (norm_fst_le φ),
      (Coeff.norm_fourierTail_le hp0 N φ.2).trans (norm_snd_le φ)⟩

theorem tendsto_pairFourierTail (hp : p ≠ ⊤) (φ : PairSpace p) :
    Filter.Tendsto (fun N : ℕ => pairFourierTail N φ) Filter.atTop (nhds 0) :=
  (Coeff.tendsto_fourierTail hp φ.1).prodMk_nhds (Coeff.tendsto_fourierTail hp φ.2)

/-- The reciprocal symbol of the first, negative-sign free component. -/
def firstFreeInverseSymbol (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    Coeff p.conjExponent := -conjugateInverseSymbol p hp (-z) (neg_notMem_freeLattice hz)

@[simp] theorem firstFreeInverseSymbol_apply (hp : p ≠ ⊤) (z : ℂ)
    (hz : z ∉ freeLattice) (j : ℤ) :
    firstFreeInverseSymbol hp z hz j = (z + (Real.pi : ℂ) * j)⁻¹ := by
  change -(-z - (Real.pi : ℂ) * j)⁻¹ = _
  rw [show -z - (Real.pi : ℂ) * j = -(z + (Real.pi : ℂ) * j) by ring, inv_neg, neg_neg]

/-- Identification with the scalar weighted-convolution sandwiches. -/
theorem doubleResolvent_apply_eq_sandwich (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ freeLattice) (f : PairSpace p) :
    doubleResolvent hp φ z hz f =
      (Coeff.convolutionSandwich (firstFreeInverseSymbol hp z hz) φ.1
          (conjugateInverseSymbol p hp z hz) f.2,
        Coeff.convolutionSandwich (conjugateInverseSymbol p hp z hz) φ.2
          (firstFreeInverseSymbol hp z hz) f.1) := by
  apply Prod.ext <;> ext j
  · rw [doubleResolvent_fst_apply, Coeff.convolutionSandwich_apply, firstFreeInverseSymbol_apply,
      ← tsum_mul_right]
    apply tsum_congr
    intro k
    change _ = φ.1 (j - k) * (f.2 k * (z - (Real.pi : ℂ) * k)⁻¹) * _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · rw [doubleResolvent_snd_apply, Coeff.convolutionSandwich_apply, ← tsum_mul_right]
    apply tsum_congr
    intro k
    rw [firstFreeInverseSymbol_apply]
    change _ = φ.2 (j - k) * (f.1 k * (z + (Real.pi : ℂ) * k)⁻¹) * (z - (Real.pi : ℂ) * j)⁻¹
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- A reciprocal free symbol loses its large part when its central window is removed. -/
theorem norm_conjugateInverseSymbol_windowTail_le (hp : p ≠ ⊤) (z : ℂ)
    (hz0 : z ∉ freeLattice) {n : ℤ} (hn : n ≠ 0) {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    ‖conjugateInverseSymbol p hp z hz0 -
      Coeff.truncate (Coeff.frequencyWindow n (n.natAbs / 2)) (conjugateInverseSymbol p hp z hz0)‖ ≤
      (8 * p.toReal / r) * (n.natAbs : ℝ) ^ (-(1 / p.toReal)) := by
  apply Coeff.norm_centered_reciprocal_windowTail_le_simple hp n.natAbs (by omega) n hr
  intro k
  change r * ‖(z - (Real.pi : ℂ) * k)⁻¹‖ ≤ _
  calc
    _ ≤ r * (r⁻¹ * (1 + |((k - n : ℤ) : ℝ)|)⁻¹) :=
      mul_le_mul_of_nonneg_left (verticalStrip_inverse_bound hr hrπ hz) hr.le
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

private theorem norm_firstFreeInverseSymbol_windowTail_le (hp : p ≠ ⊤) (z : ℂ)
    (hz0 : z ∉ freeLattice) {n : ℤ} (hn : n ≠ 0) {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    ‖firstFreeInverseSymbol hp z hz0 -
      Coeff.truncate (Coeff.frequencyWindow (-n) (n.natAbs / 2)) (firstFreeInverseSymbol hp z hz0)‖ ≤
      (8 * p.toReal / r) * (n.natAbs : ℝ) ^ (-(1 / p.toReal)) := by
  have he : firstFreeInverseSymbol hp z hz0 -
      Coeff.truncate (Coeff.frequencyWindow (-n) (n.natAbs / 2)) (firstFreeInverseSymbol hp z hz0) =
      -(conjugateInverseSymbol p hp (-z) (neg_notMem_freeLattice hz0) -
        Coeff.truncate (Coeff.frequencyWindow (-n) (n.natAbs / 2))
          (conjugateInverseSymbol p hp (-z) (neg_notMem_freeLattice hz0))) := by
    ext k
    by_cases hk : k ∈ Coeff.frequencyWindow (-n) (n.natAbs / 2) <;>
      simp [firstFreeInverseSymbol, hk]
  rw [he, norm_neg]
  simpa only [Int.natAbs_neg] using norm_conjugateInverseSymbol_windowTail_le hp (-z)
    (neg_notMem_freeLattice hz0) (neg_ne_zero.mpr hn) hr hrπ (neg_mem_verticalStrip hz)

/-- The near/far estimate with separate constants for the frequency and potential tails. -/
theorem norm_doubleResolvent_le_frequency_split (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz0 : z ∉ freeLattice) {n : ℤ} (hn : n ≠ 0) {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    ‖doubleResolvent hp φ z hz0‖ ≤
      (32 * p.toReal ^ 2 / r ^ 2) * (n.natAbs : ℝ) ^ (-(1 / p.toReal)) * ‖φ‖ +
      (4 * p.toReal ^ 2 / r ^ 2) * ‖pairFourierTail n.natAbs φ‖ := by
  let a := firstFreeInverseSymbol hp z hz0
  let b := conjugateInverseSymbol p hp z hz0
  let A := Coeff.frequencyWindow (-n) (n.natAbs / 2)
  let B := Coeff.frequencyWindow n (n.natAbs / 2)
  let F := Coeff.lowFrequencies n.natAbs
  let U := 2 * p.toReal / r
  let V := (8 * p.toReal / r) * (n.natAbs : ℝ) ^ (-(1 / p.toReal))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have ha : ‖a‖ ≤ U := by
    have h := freeL1Bound_le_verticalStrip hp z hz0 hr hrπ hz
    exact (show ‖a‖ ≤ freeL1Bound p hp z hz0 by
      simpa only [a, firstFreeInverseSymbol, norm_neg, freeL1Bound, scalarFreeL1Bound] using
        (le_max_left (scalarFreeL1Bound p hp (-z) (neg_notMem_freeLattice hz0))
          (scalarFreeL1Bound p hp z hz0))).trans h
  have hb : ‖b‖ ≤ U := (le_max_right _ _).trans
    (freeL1Bound_le_verticalStrip hp z hz0 hr hrπ hz)
  have haT : ‖a - Coeff.truncate A a‖ ≤ V :=
    norm_firstFreeInverseSymbol_windowTail_le hp z hz0 hn hr hrπ hz
  have hbT : ‖b - Coeff.truncate B b‖ ≤ V :=
    norm_conjugateInverseSymbol_windowTail_le hp z hz0 hn hr hrπ hz
  have hab := Coeff.opposite_frequencyWindows_separated n
  have hba : ∀ j ∈ B, ∀ k ∈ A, j - k ∉ F := by
    simpa only [Int.natAbs_neg, neg_neg] using Coeff.opposite_frequencyWindows_separated (-n)
  have hfirst := Coeff.norm_convolutionSandwich_le_split_of_bounds a φ.1 b A B F hab ha hb haT hbT
  have hsecond := Coeff.norm_convolutionSandwich_le_split_of_bounds b φ.2 a B A F hba hb ha hbT haT
  have hbound1 : ‖Coeff.convolutionSandwich a φ.1 b‖ ≤
      2 * U * V * ‖φ‖ + U ^ 2 * ‖pairFourierTail n.natAbs φ‖ := by
    refine hfirst.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (norm_fst_le φ) (by positivity)
    · exact mul_le_mul_of_nonneg_left (norm_fst_le (pairFourierTail n.natAbs φ)) (sq_nonneg U)
  have hbound2 : ‖Coeff.convolutionSandwich b φ.2 a‖ ≤
      2 * U * V * ‖φ‖ + U ^ 2 * ‖pairFourierTail n.natAbs φ‖ := by
    refine hsecond.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (norm_snd_le φ) (by positivity)
    · exact mul_le_mul_of_nonneg_left (norm_snd_le (pairFourierTail n.natAbs φ)) (sq_nonneg U)
  have hbound : ‖doubleResolvent hp φ z hz0‖ ≤
      2 * U * V * ‖φ‖ + U ^ 2 * ‖pairFourierTail n.natAbs φ‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    rw [doubleResolvent_apply_eq_sandwich]
    apply norm_prod_le_iff.mpr
    constructor
    · exact ((Coeff.convolutionSandwich a φ.1 b).le_opNorm f.2).trans
        (mul_le_mul hbound1 (norm_snd_le f) (norm_nonneg _) (by positivity))
    · exact ((Coeff.convolutionSandwich b φ.2 a).le_opNorm f.1).trans
        (mul_le_mul hbound2 (norm_fst_le f) (norm_nonneg _) (by positivity))
  convert hbound using 1; dsimp [U, V]; ring

/-- Chapter 1, Lemma 3.4, with the explicit constant `c_p = 32 p²` in the
maximum norm on pairs. The zero strip is covered by its full potential tail. -/
theorem norm_doubleResolvent_le_verticalStrip (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz0 : z ∉ freeLattice) {n : ℤ} {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r) :
    ‖doubleResolvent hp φ z hz0‖ ≤ (32 * p.toReal ^ 2 / r ^ 2) *
      (‖φ‖ / |(n : ℝ)| ^ (1 / p.toReal) + ‖pairFourierTail n.natAbs φ‖) := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  by_cases hn : n = 0
  · subst n
    simp only [Int.cast_zero, Int.natAbs_zero, pairFourierTail_zero,
      abs_zero, Real.zero_rpow (by positivity : 1 / p.toReal ≠ 0), div_zero, zero_add]
    calc
      _ ≤ freeL1Bound p hp z hz0 ^ 2 * ‖φ‖ := norm_doubleResolvent_le hp φ z hz0
      _ ≤ (2 * p.toReal / r) ^ 2 * ‖φ‖ := by
        gcongr
        · exact freeL1Bound_nonneg p hp z hz0
        · exact freeL1Bound_le_verticalStrip hp z hz0 hr hrπ hz
      _ ≤ (32 * p.toReal ^ 2 / r ^ 2) * ‖φ‖ := by
        gcongr
        rw [div_pow]
        apply div_le_div_of_nonneg_right _ (sq_nonneg r)
        nlinarith [sq_nonneg p.toReal]
  · have h := norm_doubleResolvent_le_frequency_split hp φ z hz0 hn hr hrπ hz
    have he : (n.natAbs : ℝ) = |(n : ℝ)| := by simp only [Nat.cast_natAbs, Int.cast_abs]
    rw [he, Real.rpow_neg (abs_nonneg _)] at h
    calc
      _ ≤ (32 * p.toReal ^ 2 / r ^ 2) * (|(n : ℝ)| ^ (1 / p.toReal))⁻¹ * ‖φ‖ +
          (4 * p.toReal ^ 2 / r ^ 2) * ‖pairFourierTail n.natAbs φ‖ := h
      _ ≤ (32 * p.toReal ^ 2 / r ^ 2) * (|(n : ℝ)| ^ (1 / p.toReal))⁻¹ * ‖φ‖ +
          (32 * p.toReal ^ 2 / r ^ 2) * ‖pairFourierTail n.natAbs φ‖ := by
        gcongr
        nlinarith [sq_nonneg p.toReal]
      _ = _ := by ring

/-- Lemma 3.4 supplies an explicit sufficient squared Neumann condition. -/
theorem squaredNeumannCondition_of_frequencyTail (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz0 : z ∉ freeLattice) {n : ℤ} {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r)
    (hφ : ‖φ‖ * ((32 * p.toReal ^ 2 / r ^ 2) *
      (‖φ‖ / |(n : ℝ)| ^ (1 / p.toReal) + ‖pairFourierTail n.natAbs φ‖)) < 1) :
    SquaredNeumannCondition hp φ z hz0 := by
  apply squaredNeumannCondition_of_doubleResolvent hp φ z hz0
  exact (mul_le_mul_of_nonneg_left
    (norm_doubleResolvent_le_verticalStrip hp φ z hz0 hr hrπ hz) (norm_nonneg _)).trans_lt hφ

/-- Under the explicit potential-tail condition, an entire punctured strip is resolvent. -/
theorem mem_resolventSet_of_frequencyTail (hp : p ≠ ⊤) (φ : PairSpace p) {z : ℂ}
    {n : ℤ} {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) (hz : z ∈ verticalStrip n r)
    (hφ : ‖φ‖ * ((32 * p.toReal ^ 2 / r ^ 2) *
      (‖φ‖ / |(n : ℝ)| ^ (1 / p.toReal) + ‖pairFourierTail n.natAbs φ‖)) < 1) :
    z ∈ resolventSet hp φ := by
  have hz0 := notMem_freeLattice_of_mem_verticalStrip hr hrπ hz
  exact mem_resolventSet_of_squaredNeumannCondition hp φ z hz0
    (squaredNeumannCondition_of_frequencyTail hp φ z hz0 hr hrπ hz hφ)

/-- A spectral circle is admissible whenever the corresponding frequency-tail bound is small. -/
theorem sphere_subset_resolventSet_of_frequencyTail (hp : p ≠ ⊤) (φ : PairSpace p)
    (n : ℤ) {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    (hφ : ‖φ‖ * ((32 * p.toReal ^ 2 / r ^ 2) *
      (‖φ‖ / |(n : ℝ)| ^ (1 / p.toReal) + ‖pairFourierTail n.natAbs φ‖)) < 1) :
    Metric.sphere ((Real.pi : ℂ) * n) r ⊆ resolventSet hp φ := by
  intro z hz
  exact mem_resolventSet_of_frequencyTail hp φ hr hrπ (sphere_subset_verticalStrip n hrπ hz) hφ

end NLS.ZakharovShabat
