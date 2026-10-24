import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Smooth cutoffs under positive dilation -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace NLS.FunctionalAnalysis

/-- A fixed smooth cutoff, equal to one on the unit interval. -/
def unitSmoothCutoff (t : ℝ) : ℂ := ((default : ContDiffBump (0 : ℝ)) t : ℂ)

theorem contDiff_unitSmoothCutoff : ContDiff ℝ 1 unitSmoothCutoff :=
  Complex.ofRealCLM.contDiff.comp (default : ContDiffBump (0 : ℝ)).contDiff

theorem hasCompactSupport_unitSmoothCutoff : HasCompactSupport unitSmoothCutoff :=
  (default : ContDiffBump (0 : ℝ)).hasCompactSupport.comp_left (by simp)

theorem unitSmoothCutoff_eq_one {t : ℝ} (ht : t ∈ Icc 0 1) :
    unitSmoothCutoff t = 1 := by
  have h : (default : ContDiffBump (0 : ℝ)) t = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    change dist t 0 ≤ 1
    simpa [Real.dist_eq, abs_of_nonneg ht.1] using ht.2
  simp [unitSmoothCutoff,h]

/-- Dilation of a scalar cutoff by a positive real scale. -/
def scaledCutoff (χ : ℝ → ℂ) (R t : ℝ) : ℂ := χ (t / R)

theorem contDiff_scaledCutoff (χ : ℝ → ℂ) (hχ : ContDiff ℝ 1 χ) (R : ℝ) :
    ContDiff ℝ 1 (scaledCutoff χ R) :=
  hχ.comp (contDiff_id.div_const R)

theorem hasCompactSupport_scaledCutoff (χ : ℝ → ℂ) (hχ : HasCompactSupport χ)
    (R : ℝ) (hR : R ≠ 0) : HasCompactSupport (scaledCutoff χ R) := by
  change HasCompactSupport (fun t => χ (t/R))
  simpa only [Function.comp_def,Homeomorph.coe_mulRight₀,← div_eq_mul_inv] using!
    hχ.comp_homeomorph (Homeomorph.mulRight₀ R⁻¹ (inv_ne_zero hR))

theorem deriv_scaledCutoff (χ : ℝ → ℂ) (hχ : ContDiff ℝ 1 χ) (R t : ℝ) :
    deriv (scaledCutoff χ R) t = R⁻¹ • deriv χ (t/R) := by
  simpa only [scaledCutoff,one_div] using!
    ((hχ.differentiable one_ne_zero (t/R)).hasDerivAt.scomp t
      ((hasDerivAt_id t).div_const R)).deriv

/-- The squared derivative integral decreases inversely with the scale. -/
theorem integral_sq_deriv_scaledCutoff (χ : ℝ → ℂ) (hχ : ContDiff ℝ 1 χ)
    (R : ℝ) (hR : 0 < R) :
    (∫ t : ℝ, ‖deriv (scaledCutoff χ R) t‖ ^ 2) =
      (∫ t : ℝ, ‖deriv χ t‖ ^ 2) / R := by
  simp_rw [deriv_scaledCutoff χ hχ R,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR),mul_pow]
  rw [integral_const_mul,Measure.integral_comp_div (fun t => ‖deriv χ t‖ ^ 2),abs_of_pos hR]
  simp only [smul_eq_mul]
  field_simp

/-- The dilated fixed cutoff is one throughout the expanding interval. -/
theorem scaled_unitSmoothCutoff_eq_one (R : ℝ) (hR : 0 < R)
    {t : ℝ} (ht : t ∈ Icc 0 R) : scaledCutoff unitSmoothCutoff R t = 1 := by
  apply unitSmoothCutoff_eq_one
  exact ⟨div_nonneg ht.1 hR.le,(div_le_one hR).mpr ht.2⟩

end NLS.FunctionalAnalysis
