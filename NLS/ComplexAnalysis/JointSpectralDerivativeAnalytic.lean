import NLS.ComplexAnalysis.JointSpectralDerivative
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! Joint analyticity of the spectral derivative, extending the retained continuity API. -/
noncomputable section
namespace NLS.ComplexAnalysis
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
theorem analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (F : ℂ × A → ℂ) (D : Set (ℂ × A))
    (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D) :
    AnalyticOnNhd ℂ (fun t : ℂ × A =>
      deriv (fun w : ℂ => F (w,t.2)) t.1) D := by
  let ev : ((ℂ × A) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1,0)
  have hder := ev.comp_analyticOnNhd hF.fderiv
  intro t ht
  apply (hder t ht).congr
  filter_upwards [hD.mem_nhds ht] with u hu
  exact (deriv_spectral_section_eq_fderiv F u.1 u.2 (hF u hu).differentiableAt).symm


end NLS.ComplexAnalysis
