import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Complex.Basic

/-! # Intrinsic action derivatives from recovery on positive real rays

A positive real ray determines the complex directional derivative at its
endpoint. This applies at boundary points of infinite dimensional action cones.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The derivative along an actual unscaled real action line. -/
theorem hasDerivAt_comp_real_action_line (f : E → ℂ) (x v : E)
    (hf : DifferentiableAt ℂ f x) :
    HasDerivAt (fun t : ℝ => f (x+(t : ℂ) • v)) ((fderiv ℂ f x) v) 0 := by
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ)))
  have hline : HasDerivAt (fun t : ℝ => x+(t : ℂ) • v) v 0 := by
    simpa only [one_smul] using! (ht.smul_const v).const_add x
  have hdf : HasFDerivAt f ((fderiv ℂ f x).restrictScalars ℝ) (x+(0 : ℂ) • v) := by
    simpa only [zero_smul,add_zero] using! hf.hasFDerivAt.restrictScalars ℝ
  simpa only [Function.comp_def] using! hdf.comp_hasDerivAt 0 hline

/-- Recovery on the entire positive real ray fixes the complex derivative,
including when the starting action is zero. -/
theorem fderiv_eq_of_positive_action_ray (f g : E → ℂ) (x v : E)
    (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x)
    (he : ∀ t : ℝ, 0 ≤ t → f (x+(t : ℂ) • v) = g (x+(t : ℂ) • v)) :
    (fderiv ℂ f x) v = (fderiv ℂ g x) v := by
  have hdf := hasDerivAt_comp_real_action_line f x v hf
  have hdg := hasDerivAt_comp_real_action_line g x v hg
  have hdg' := hdg.hasDerivWithinAt.congr (fun t ht => he t ht) (he 0 le_rfl)
  exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hdf.hasDerivWithinAt hdg'

/-- Real physical values on a positive ray force its action derivative to
be real, even at a closed action. -/
theorem fderiv_im_eq_zero_of_positive_action_ray (f : E → ℂ) (x v : E)
    (hf : DifferentiableAt ℂ f x)
    (hreal : ∀ t : ℝ, 0 ≤ t → (f (x+(t : ℂ) • v)).im = 0) :
    ((fderiv ℂ f x) v).im = 0 := by
  have hd := hasDerivAt_comp_real_action_line f x v hf
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  have hz : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Ici 0) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt
  have hz' := hz.congr (fun t ht => hreal t ht) (hreal 0 le_rfl)
  exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ him.hasDerivWithinAt hz'

end NLS.ComplexAnalysis
