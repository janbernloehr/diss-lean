import NLS.ComplexAnalysis.MovingSpectralParameter

/-! A moving spectral evaluation after a bounded linear source
restriction. Opaque source functions keep the full chain rule independent
of their concrete spectral constructions. -/
noncomputable section
open Filter Topology
namespace NLS.FunctionalAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem fderiv_linear_pullback_moving_spectral
    (N s : F → ℂ) (T : ℂ × E → ℂ) (L : E →L[ℂ] F) (a h : E)
    (hN : DifferentiableAt ℂ N (L a)) (hs : DifferentiableAt ℂ s (L a))
    (hT : DifferentiableAt ℂ T (s (L a),a))
    (he : (fun b => N (L b)) =ᶠ[𝓝 a] (fun b => T (s (L b),b))) :
    (fderiv ℂ N (L a)) (L h)=
      (fderiv ℂ (fun b => T (s (L a),b)) a) h+
        deriv (fun z => T (z,a)) (s (L a))*(fderiv ℂ s (L a)) (L h) := by
  have hNc := (hN.hasFDerivAt.comp a L.hasFDerivAt).fderiv
  have hsc := (hs.hasFDerivAt.comp a L.hasFDerivAt).fderiv
  have hsd : DifferentiableAt ℂ (fun b => s (L b)) a := hs.comp a L.differentiableAt
  have hm := NLS.ComplexAnalysis.fderiv_moving_spectral_parameter T (fun b => s (L b)) a hT hsd
  change fderiv ℂ (fun b => N (L b)) a=_ at hNc
  change fderiv ℂ (fun b => s (L b)) a=_ at hsc
  rw [he.fderiv_eq,hm,hsc] at hNc
  have hh := congrArg (fun M : E →L[ℂ] ℂ => M h) hNc
  simpa only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply] using hh.symm

end NLS.FunctionalAnalysis
