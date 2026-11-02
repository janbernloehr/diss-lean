import NLS.KdV.PseudomeasureSpectralLipschitz

/-! Spectral variation of the ACTUAL off-diagonal physical Hill coupling. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- The full spectral variation bound retains the off-diagonal Sobolev factor. -/
theorem endpointUpperCoupling_sub_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z y : ℂ) (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ‖endpointUpperCoupling r hr hr1 n (q,z)-endpointUpperCoupling r hr hr1 n (q,y)‖ ≤
      (Weight.sobolev r (2*(n:ℤ))*(4*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(n:ℝ)⁻¹*‖q‖))*‖z-y‖ := by
  have hc := negativeShiftedNorm_coefficient_le SpectralWeight.one r hr (n:ℤ) n
    (endpointHillCorrectedMode SpectralWeight.one r hr hr1 n hn z hz q hs (-(n:ℤ))-
      endpointHillCorrectedMode SpectralWeight.one r hr hr1 n hn y hy q hs (-(n:ℤ)))
  have ht := negativeShiftedNorm_endpointHillCorrectedMode_sub_le SpectralWeight.one r hr hr1
    n hn z y hz hy q hs (-(n:ℤ)) (Or.inr rfl)
  have hh := hc.trans (by simpa only [neg_neg] using ht)
  rw [endpointHillCorrectedMode_neg, endpointHillCorrectedMode_neg, WeightedCoeff.sub_val,
    show (n:ℤ)+n = 2*(n:ℤ) by ring] at hh
  have hdiv : ‖endpointUpperCoupling r hr hr1 n (q,z)-endpointUpperCoupling r hr hr1 n (q,y)‖ /
      Weight.sobolev r (2*(n:ℤ)) ≤
      (4*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(n:ℝ)⁻¹*‖q‖)*‖z-y‖ := by
    simpa only [endpointUpperCoupling, endpointEffectiveFamily_eq r hr hr1 n hn (q,z) hz hs,
      endpointEffectiveFamily_eq r hr hr1 n hn (q,y) hy hs,
      SpectralWeight.negativeSobolev_apply, SpectralWeight.one_apply, one_div, one_mul, div_eq_mul_inv,
      mul_comm] using hh
  have hW := (Weight.sobolev r).positive (2*(n:ℤ))
  exact ((div_le_iff₀ hW).mp hdiv).trans_eq (by ring)

/-- The SAME original half-contraction cutoff makes the actual coupling
1/8-Lipschitz on the ENTIRE corrected strip. No further cutoff is assumed. -/
theorem endpointUpperCoupling_sub_le_eighth (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z y : ℂ) (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ‖endpointUpperCoupling r hr hr1 n (q,z)-endpointUpperCoupling r hr hr1 n (q,y)‖ ≤ (1/8:ℝ)*‖z-y‖ := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hM := endpoint_effective_column_small r hr hr1 n hn q hs
  have hSQ : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hfrac : Weight.sobolev r (2*(n:ℤ))*‖q‖/(n:ℝ) ≤ 1/16 :=
    (div_le_iff₀ hnpos).mpr (by nlinarith)
  have hc : Weight.sobolev r (2*(n:ℤ))*(4*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(n:ℝ)⁻¹*‖q‖) ≤ (1/8:ℝ) := by
    calc
      _ = 4*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(Weight.sobolev r (2*(n:ℤ))*‖q‖/(n:ℝ)) := by ring
      _ ≤ 4*(1/2:ℝ)*(Weight.sobolev r (2*(n:ℤ))*‖q‖/(n:ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith [hs])
          (div_nonneg (mul_nonneg ((Weight.sobolev r).positive _).le (norm_nonneg q)) hnpos.le)
      _ ≤ 4*(1/2:ℝ)*(1/16) := mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = _ := by norm_num
  exact (endpointUpperCoupling_sub_le r hr hr1 n hn z y hz hy q hs).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

end NLS.KdV
