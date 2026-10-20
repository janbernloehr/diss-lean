import NLS.ComplexAnalysis.TwoRootQuotientDiscBound
import NLS.ZakharovShabat.DeletedPeriodicFree
import Mathlib.Tactic.LinearCombination

/-! # The deleted periodic product on a spectral disc

A squared-discriminant contour estimate controls the actual deleted periodic product throughout its disc, including collapsed gaps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A circle estimate for the actual discriminant gives a comparison
of its entire deleted periodic product throughout the disc. The removed
endpoints may coincide, so this estimate also applies to collapsed gaps. -/
theorem norm_canonicalDeletedPeriodicProduct_sub_free_on_closedDisc
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) (r ε A B : ℝ)
    (hr : 0 < r) (hε : 0 ≤ ε) (hεr : ε ≤ r/2) (hB : 0 ≤ B)
    (ha : ‖canonicalPeriodicLeft hp hp1 φ heven n-(Real.pi:ℂ)*n‖ ≤ ε)
    (hb : ‖canonicalPeriodicRight hp hp1 φ heven n-(Real.pi:ℂ)*n‖ ≤ ε)
    (herror : ∀ z ∈ sphere ((Real.pi:ℂ)*n) r,
      ‖(canonicalDiscriminant hp φ z)^2-(freeDiscriminant z)^2‖ ≤ A)
    (hmodel : ∀ z ∈ sphere ((Real.pi:ℂ)*n) r, ‖(freeSineQuotient n z)^2‖ ≤ B)
    (z : ℂ) (hz : ‖z-(Real.pi:ℂ)*n‖ ≤ r) :
    ‖canonicalDeletedPeriodicProduct hp hp1 φ heven n z-(freeSineQuotient n z)^2‖ ≤
      4*(A/4+B*(2*r*ε+ε^2))/r^2 := by
  let Q := canonicalDeletedPeriodicProduct hp hp1 φ heven n
  let Q₀ := canonicalDeletedPeriodicProduct hp hp1 0 (pairParitySubspace 0).zero_mem n
  let F (w : ℂ) := -((canonicalDiscriminant hp φ w)^2-4)/4
  let F₀ (w : ℂ) := -((freeDiscriminant w)^2-4)/4
  have hQ : Differentiable ℂ Q := fun w =>
    (analyticOnNhd_canonicalDeletedPeriodicProduct hp hp1 φ heven n w (mem_univ _)).differentiableAt
  have hQ₀ : Differentiable ℂ Q₀ := fun w =>
    (analyticOnNhd_canonicalDeletedPeriodicProduct hp hp1 0 (pairParitySubspace 0).zero_mem n w (mem_univ _)).differentiableAt
  have hF (w : ℂ) : F w =
      (w-canonicalPeriodicLeft hp hp1 φ heven n)*(w-canonicalPeriodicRight hp hp1 φ heven n)*Q w := by
    have h := canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 φ heven n w
    dsimp only [F,Q]
    linear_combination (-1/4:ℂ)*h
  have hF₀ (w : ℂ) : F₀ w = (w-(Real.pi:ℂ)*n)^2*Q₀ w := by
    have h := canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 0 (pairParitySubspace 0).zero_mem n w
    simp only [canonicalDiscriminant_zero_finite,canonicalPeriodicLeft_zero,canonicalPeriodicRight_zero] at h
    dsimp only [F₀,Q₀]
    linear_combination (-1/4:ℂ)*h
  have he (w : ℂ) (hw : w ∈ sphere ((Real.pi:ℂ)*n) r) : ‖F w-F₀ w‖ ≤ A/4 := by
    rw [show F w-F₀ w = -((canonicalDiscriminant hp φ w)^2-(freeDiscriminant w)^2)/4 by dsimp [F,F₀]; ring]
    rw [norm_div,norm_neg,norm_ofNat]
    exact div_le_div_of_nonneg_right (herror w hw) (by norm_num)
  have hm (w : ℂ) (hw : w ∈ sphere ((Real.pi:ℂ)*n) r) : ‖Q₀ w‖ ≤ B := by
    simpa only [Q₀,canonicalDeletedPeriodicProduct_zero] using hmodel w hw
  have h := NLS.ComplexAnalysis.norm_two_root_quotient_sub_le_on_closedDisc
    F F₀ Q Q₀ _ _ ((Real.pi:ℂ)*n) r ε (A/4) B hr hε hεr hB ha hb hQ hQ₀ hF hF₀ he hm z hz
  simpa only [Q,Q₀,canonicalDeletedPeriodicProduct_zero] using h

end NLS.ZakharovShabat
