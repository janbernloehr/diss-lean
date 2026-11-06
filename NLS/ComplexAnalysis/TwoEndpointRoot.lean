import NLS.ComplexAnalysis.RealCutConjugation
import NLS.ZakharovShabat.SourceStandardRootAnalytic
import NLS.ZakharovShabat.SourceStandardRootGapSideMidpoint

/-! # The standard root of an arbitrary endpoint pair

These statements use the existing normalized standard root, without
source-specific endpoint labels. The vertical midpoint formula fixes
both half-plane signs, also when the two real endpoints coincide.
-/
noncomputable section
set_option autoImplicit false
open Set Complex ComplexOrder NLS.ZakharovShabat
namespace NLS.ComplexAnalysis

theorem pair_midpoint_mem_segment (l u : ℂ) : (l+u)/2 ∈ segment ℝ l u := by
  convert midpoint_mem_segment (𝕜 := ℝ) l u using 1
  rw [midpoint_eq_smul_add, invOf_eq_inv]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_ofNat]
  ring

theorem normalizedStandardRoot_sq_off_segment (l u z : ℂ) (hz : z ∉ segment ℝ l u) :
    normalizedStandardRoot ((l+u)/2) ((u-l)^2) z^2 = (z-l)*(z-u) := by
  have hm : (l+u)/2 ≠ z := fun he => hz (he ▸ pair_midpoint_mem_segment l u)
  rw [normalizedStandardRoot_sq _ _ _ hm]
  ring

theorem analyticOnNhd_standardRoot_off_segment (l u : ℂ) :
    AnalyticOnNhd ℂ (normalizedStandardRoot ((l+u)/2) ((u-l)^2)) (segment ℝ l u)ᶜ := by
  intro z hz
  exact normalizedStandardRoot_analyticAt_of_slit _ _ _
    (fun he => hz (he ▸ pair_midpoint_mem_segment l u))
    (gap_radicand_mem_slitPlane l u z hz)

/-- Both vertical midpoint values have a strict imaginary sign. No
positive gap-length assumption is imposed. -/
theorem exists_standardRoot_vertical_midpoint_value (t : ℂ) (d y : ℝ) (hy : 0 < y) :
    ∃ a : ℝ, 0 < a ∧
      normalizedStandardRoot t ((2*(d : ℂ))^2) (t+(y : ℂ)*I) = -(a : ℂ)*I ∧
      normalizedStandardRoot t ((2*(d : ℂ))^2) (t-(y : ℂ)*I) = (a : ℂ)*I := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hp : 0 < 1+d^2/y^2 := by positivity
  have hrad : 1-(2*(d : ℂ))^2/(4*(t-(t+(y : ℂ)*I))^2) =
      ((1+d^2/y^2 : ℝ) : ℂ) := by
    rw [show t-(t+(y : ℂ)*I) = -(y : ℂ)*I by ring]
    push_cast
    field_simp [hyC,I_sq]
    rw [I_sq]
    ring

  have hu : normalizedStandardRoot t ((2*(d : ℂ))^2) (t+(y : ℂ)*I) =
      -((y*Real.sqrt (1+d^2/y^2) : ℝ) : ℂ)*I := by
    rw [normalizedStandardRoot,hrad,Complex.sqrt_of_nonneg (by exact_mod_cast hp.le)]
    simp only [Complex.ofReal_re]
    push_cast
    ring
  refine ⟨y*Real.sqrt (1+d^2/y^2),mul_pos hy (Real.sqrt_pos.mpr hp),hu,?_⟩
  have he : t-(y : ℂ)*I = 2*t-(t+(y : ℂ)*I) := by ring
  rw [he,normalizedStandardRoot_reflect,hu]
  ring

end NLS.ComplexAnalysis
