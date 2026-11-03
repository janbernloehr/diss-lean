import NLS.ComplexAnalysis.JointSpectralDerivative
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (F : ℂ × A → ℂ) (D : Set (ℂ × A)) (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D) :
    AnalyticOnNhd ℂ (fun t : ℂ × A => deriv (fun w : ℂ => F (w,t.2)) t.1) D := by
  let C : ((ℂ × A) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1,(0 : A))
  have hG := C.comp_analyticOnNhd hF.fderiv
  apply AnalyticOnNhd.congr hD hG
  intro t ht
  exact (deriv_spectral_section_eq_fderiv F t.1 t.2 (hF t ht).differentiableAt).symm

end NLS.ComplexAnalysis
