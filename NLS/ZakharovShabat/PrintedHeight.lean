import NLS.ZakharovShabat.ExplicitHeight
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # The printed spectral height for exponents between one and two

Convexity in the exponent closes the numerical Neumann estimate throughout
1 ≤ p ≤ 2. Above two the same numerical criterion fails at sufficiently large
norms; this is a limitation of the criterion, not a spectral counterexample.
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Interpolate the endpoint scalar estimates in the exponent. -/
theorem printed_height_neumann_bound {q M : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hM : 0 ≤ M) :
    (4*q / ((1+8*M)^q)^(1/q) + 1/(1+8*M)^q)*M < 1 := by
  let B := 1+8*M
  have hB : 0 < B := by dsimp [B]; positivity
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hroot : (B^q)^(1/q) = B := by
    rw [← Real.rpow_mul hB.le,mul_one_div_cancel hq.ne',Real.rpow_one]
  change (4*q / (B^q)^(1/q) + 1/B^q)*M < 1
  rw [hroot]
  have hc := (convexOn_rpow_left (inv_pos.mpr hB)).2 (Set.mem_univ (1:ℝ)) (Set.mem_univ (2:ℝ))
    (by linarith : 0 ≤ 2-q) (by linarith : 0 ≤ q-1) (by ring : (2-q)+(q-1)=1)
  have he : (2-q)*(1:ℝ)+(q-1)*2 = q := by ring
  simp only [smul_eq_mul,he,Real.rpow_one,Real.rpow_two,Real.inv_rpow hB.le] at hc
  have h1 : (4/B+1/B)*M < 1 := by
    dsimp [B]
    rw [← add_div,div_mul_eq_mul_div]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have h2 : (8/B+1/B^2)*M < 1 := hilbert_height_neumann_bound hM
  have hw : (2-q)*((4/B+1/B)*M)+(q-1)*((8/B+1/B^2)*M) < 1 := by
    have ha := mul_le_mul_of_nonneg_left h1.le (by linarith : 0 ≤ 2-q)
    have hb := mul_le_mul_of_nonneg_left h2.le (by linarith : 0 ≤ q-1)
    by_cases heq : q = 1
    · subst q
      convert h1 using 1
      ring
    · have hb' := mul_lt_mul_of_pos_left h2 (sub_pos.mpr (lt_of_le_of_ne hq1 (Ne.symm heq)))
      nlinarith
  have hbnd : (4*q/B+1/B^q)*M ≤
      (2-q)*((4/B+1/B)*M)+(q-1)*((8/B+1/B^2)*M) := by
    have hh := mul_le_mul_of_nonneg_right hc hM
    simp only [div_eq_mul_inv,one_mul] at ⊢
    nlinarith [hh]
  exact hbnd.trans_lt hw

/-- Above two, sufficiently large norms fail this particular Neumann criterion
at the printed height. This does not assert the presence of an eigenvalue. -/
theorem printed_height_neumann_bound_fails {q M : ℝ} (hq : 2 < q)
    (hM : 1/(4*q-8) ≤ M) :
    1 < (4*q / ((1+8*M)^q)^(1/q) + 1/(1+8*M)^q)*M := by
  have hd : 0 < 4*q-8 := by linarith
  have hMpos : 0 < M := (one_div_pos.mpr hd).trans_le hM
  have hB : 0 < 1+8*M := by positivity
  have hroot : (((1+8*M)^q)^(1/q)) = 1+8*M := by
    rw [← Real.rpow_mul hB.le,mul_one_div_cancel (by linarith : q ≠ 0),Real.rpow_one]
  rw [hroot]
  have hm := (div_le_iff₀ hd).mp hM
  have hfirst : 1 ≤ 4*q/(1+8*M)*M := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hB).mpr
    nlinarith
  have hlast : 0 < (1/(1+8*M)^q)*M := by positivity
  nlinarith

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The printed height is in the numerical Neumann region for 1 ≤ p ≤ 2. -/
theorem mem_heightNeumannRegion_of_printed_height (hp : p ≠ ⊤) (hp2 : p ≤ 2)
    (φ : PairSpace p) {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : (1+8*M)^p.toReal ≤ |z.im|) : z ∈ heightNeumannRegion φ := by
  have hM := (norm_nonneg φ).trans hφ
  have hpr1 : 1 ≤ p.toReal := by exact_mod_cast ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hpr2 : p.toReal ≤ 2 := by exact_mod_cast ENNReal.toReal_mono (by simp) hp2
  apply mem_heightNeumannRegion_of_height_le hp φ (by positivity) _ hz
  exact (mul_le_mul_of_nonneg_left hφ (by positivity)).trans_lt
    (printed_height_neumann_bound hpr1 hpr2 hM)

/-- The resolvent exists on and above both printed horizontal edges for 1 ≤ p ≤ 2. -/
theorem mem_resolventSet_of_printed_height (hp : p ≠ ⊤) (hp2 : p ≤ 2)
    (φ : PairSpace p) {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : (1+8*M)^p.toReal ≤ |z.im|) : z ∈ resolventSet hp φ :=
  heightNeumannRegion_subset_resolventSet hp φ
    (mem_heightNeumannRegion_of_printed_height hp hp2 φ hφ hz)

/-- The full periodic spectrum lies strictly within the printed strip for 1 ≤ p ≤ 2. -/
theorem abs_im_lt_printed_height (hp : p ≠ ⊤) (hp2 : p ≤ 2)
    (φ : PairSpace p) {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : z ∈ periodicSpectrum hp φ) : |z.im| < (1+8*M)^p.toReal := by
  by_contra h
  exact hz (mem_resolventSet_of_printed_height hp hp2 φ hφ (le_of_not_gt h))

end NLS.ZakharovShabat
