import NLS.SequenceSpaces.SobolevPowerMultiplier
import NLS.ZakharovShabat.SourceNormalizedActionH1Decay

/-! # Two-derivative smoothing of normalization errors

On each physical H1 ball, multiplication by the actual root error or
inverse-root error gains two sequence derivatives, at every real order
and Banach exponent including infinity. Inversion does not increase the
root error on any real source at any finite exponent greater than one.
-/

noncomputable section
open Set Metric Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Inverting the positive actual normalized root cannot increase its error from one. -/
theorem sourceNormalizedActionRoot_inverse_deviation_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    ‖(sourceNormalizedActionRoot hp hp1 n φ.val)⁻¹-1‖ ≤ ‖sourceNormalizedActionRoot hp hp1 n φ.val-1‖ := by
  let ξ := sourceNormalizedActionRoot hp hp1 n φ.val
  have hre : 1 ≤ ξ.re := sourceNormalizedActionRoot_re_ge_one hp hp1 φ n
  have hξ : ξ ≠ 0 := by intro h; rw [h,Complex.zero_re] at hre; linarith
  have he : ξ⁻¹-1 = ξ⁻¹*(1-ξ) := by rw [mul_sub,mul_one,inv_mul_cancel₀ hξ]
  change ‖ξ⁻¹-1‖ ≤ ‖ξ-1‖
  rw [he,norm_mul]
  calc
    _ ≤ 1*‖1-ξ‖ := mul_le_mul_of_nonneg_right (sourceNormalizedActionRoot_inverse_norm_le_one hp hp1 φ n) (norm_nonneg _)
    _ = _ := by rw [one_mul,norm_sub_rev]

/-- Both normalization-error multipliers gain two derivatives uniformly on physical H1 balls. -/
theorem sourceNormalizedActionRoot_multipliers_uniform_physical_H1_ball (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ (q : ℝ≥0∞) (_ : Fact (1 ≤ q)) (r : ℝ),
        ∃ T S : WeightedCoeff (Weight.sobolev r) q →L[ℂ] WeightedCoeff (Weight.sobolev (r+2)) q,
          (∀ c n, (T c).val n = (sourceNormalizedActionRoot (by simp) (by norm_num) n (sobolevSourceInclusion a.val)-1)*c.val n) ∧
          (∀ c n, (S c).val n = ((sourceNormalizedActionRoot (by simp) (by norm_num) n (sobolevSourceInclusion a.val))⁻¹-1)*c.val n) ∧
          ‖T‖ ≤ K ∧ ‖S‖ ≤ K := by
  obtain ⟨K,hK,h⟩ := sourceNormalizedActionRoot_uniform_physical_H1_decay R
  refine ⟨K,hK,?_⟩
  intro a ha q hq r
  obtain ⟨T,hT,hnT⟩ := WeightedCoeff.exists_sobolev_power_multiplier (p := q) r 2
    (fun n => sourceNormalizedActionRoot (by simp) (by norm_num) n (sobolevSourceInclusion a.val)-1) K hK
    (fun n => by simpa only [Real.rpow_two] using h a ha n)
  obtain ⟨S,hS,hnS⟩ := WeightedCoeff.exists_sobolev_power_multiplier (p := q) r 2
    (fun n => (sourceNormalizedActionRoot (by simp) (by norm_num) n (sobolevSourceInclusion a.val))⁻¹-1) K hK
    (fun n => by
      rw [Real.rpow_two]
      exact (mul_le_mul_of_nonneg_left (sourceNormalizedActionRoot_inverse_deviation_le (by simp) (by norm_num)
        (sourceH1RealSource a) n) (sq_nonneg (1+|(n:ℝ)|))).trans (h a ha n))
  exact ⟨T,S,hT,hS,hnT,hnS⟩

end NLS.ZakharovShabat
