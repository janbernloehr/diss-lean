import NLS.Articles.KdVConvexity.ActionHilbertGradientCoordinates
import NLS.Articles.KdVConvexity.PhysicalTaylorAtZero

/-! The intrinsic physical Taylor operator in exact unweighted integer
coordinates enumerating ALL positive action labels. -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity

theorem PhysicalHstarExtension.normalized_gradient_Taylor (E : PhysicalHstarExtension) :
    normalizedActionGradient E.hamiltonian 0=0 ∧
      fderiv ℂ (normalizedActionGradient E.hamiltonian) 0=
        (-6 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 2) := by
  constructor
  · simp only [normalizedActionGradient,map_zero,E.Taylor_at_zero.2.1]
  · have hH : AnalyticAt ℂ E.hamiltonian (actionUnreindex (0 : Coeff 2)) := by
      rw [map_zero]
      exact E.analytic 0 (E.contains_cone zero_mem_positiveQuadrant)
    have hz : fderiv ℂ (normalizedActionGradient E.hamiltonian) 0+
        (6 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 2)=0 := by
      rw [normalizedActionGradient_corrected_derivative E.hamiltonian 0 hH 6,map_zero,E.Taylor_at_zero.2.2,
        ←add_smul]
      norm_num
    have he := congrArg (fun A : Coeff 2 →L[ℂ] Coeff 2 => A-(6 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 2)) hz
    simpa only [add_sub_cancel_right,zero_sub,←neg_smul] using he

end NLS.Articles.KdVConvexity
