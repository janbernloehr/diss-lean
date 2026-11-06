import NLS.ComplexAnalysis.TranslationCovariantCotangent

/-! # Annihilators at a stationary equivariant vector field

Differentiating dF Xi = R F where Xi vanishes removes the Hessian term.
A cotangent annihilating dF then also annihilates R dF. The identity on
a real form extends to every complex variation in its span.
-/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis
variable {H E F : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem annihilator_rotation_of_stationary_equivariance
    (V : Submodule ℝ H)
    (hspan : ∀ h : H, ∃ x y : V, h = x.val+I • y.val)
    (J : H →L[ℂ] E) (R : F →L[ℂ] F) (f : E → F) (Xi : E → E) (a : V)
    (hf : AnalyticAt ℂ f (J a.val)) (hXi : DifferentiableAt ℂ Xi (J a.val))
    (hcov : ∀ b : V, (fderiv ℂ f (J b.val)) (Xi (J b.val)) = R (f (J b.val)))
    (hstationary : Xi (J a.val) = 0)
    (L : F →L[ℂ] ℂ) (hL : L.comp (fderiv ℂ f (J a.val)) = 0) :
    ((L.comp R).comp (fderiv ℂ f (J a.val))).comp J = 0 := by
  let A := fderiv ℂ f (J a.val)
  let B := fderiv ℂ (fderiv ℂ f) (J a.val)
  have hd := ((hf.fderiv.differentiableAt.hasFDerivAt.comp a.val J.hasFDerivAt).clm_apply
    (hXi.hasFDerivAt.comp a.val J.hasFDerivAt)).restrictScalars ℝ
  have hr := (R.hasFDerivAt.comp a.val
    (hf.differentiableAt.hasFDerivAt.comp a.val J.hasFDerivAt)).restrictScalars ℝ
  have hdV := hd.comp a V.subtypeL.hasFDerivAt
  have hrV := hr.comp a V.subtypeL.hasFDerivAt
  have he : (fun b : V => (fderiv ℂ f (J b.val)) (Xi (J b.val))) =
      (fun b : V => R (f (J b.val))) := funext hcov
  change HasFDerivAt (fun b : V => (fderiv ℂ f (J b.val)) (Xi (J b.val))) _ a at hdV
  change HasFDerivAt (fun b : V => R (f (J b.val))) _ a at hrV
  rw [he] at hdV
  have hreal (h : V) : L (R (A (J h.val))) = 0 := by
    have hh := congrArg (fun T : V →L[ℝ] F => T h) (hdV.unique hrV)
    change A ((fderiv ℂ Xi (J a.val)) (J h.val))+
      B (J h.val) (Xi (J a.val)) = R (A (J h.val)) at hh
    rw [hstationary,map_zero,add_zero] at hh
    rw [← hh]
    exact congrArg (fun T : E →L[ℂ] ℂ => T ((fderiv ℂ Xi (J a.val)) (J h.val))) hL
  apply ContinuousLinearMap.ext
  intro h
  obtain ⟨x,y,rfl⟩ := hspan h
  change L (R (A (J (x.val+I • y.val)))) = 0
  simp only [map_add,map_smul,hreal,smul_zero,add_zero]

end NLS.ComplexAnalysis
