import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Exact derivatives of commuting diagrams with continuous linear vertical
maps, and the derivative identity of a differentiable inverse. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem fderiv_commuting_square (f : E → F) (g : G → H)
    (L : E →L[ℝ] G) (R : F →L[ℝ] H) (x v : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (L x))
    (he : ∀ y, R (f y)=g (L y)) :
    R ((fderiv ℝ f x) v)=(fderiv ℝ g (L x)) (L v) := by
  have hl := R.hasFDerivAt.comp x hf.hasFDerivAt
  have hr := hg.hasFDerivAt.comp x L.hasFDerivAt
  have hfun : R ∘ f=g ∘ L := funext he
  rw [hfun] at hl
  exact congrArg (fun A : E →L[ℝ] H => A v) (hl.unique hr)

theorem fderiv_inverse_apply (f : E → F) (g : F → E) (y v : F)
    (hf : DifferentiableAt ℝ f (g y)) (hg : DifferentiableAt ℝ g y)
    (he : ∀ z, f (g z)=z) :
    (fderiv ℝ f (g y)) ((fderiv ℝ g y) v)=v := by
  have hd := hf.hasFDerivAt.comp y hg.hasFDerivAt
  have hfun : f ∘ g=(fun z : F => z) := funext he
  rw [hfun] at hd
  exact congrArg (fun A : F →L[ℝ] F => A v) (hd.unique (hasFDerivAt_id y))

theorem hasDerivAt_map_real_ray (f : E → F) (v : E) (hf : DifferentiableAt ℝ f 0) :
    HasDerivAt (fun t : ℝ => f (t • v)) ((fderiv ℝ f 0) v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [one_smul,id_eq] using! (hasDerivAt_id (0:ℝ)).smul_const v
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)

theorem fderiv_clm_after_apply (f : E → F) (L : F →L[ℝ] G) (x v : E)
    (hf : DifferentiableAt ℝ f x) :
    (fderiv ℝ (fun y => L (f y)) x) v=L ((fderiv ℝ f x) v) := by
  have hd := L.hasFDerivAt.comp x hf.hasFDerivAt
  exact congrArg (fun A : E →L[ℝ] G => A v) hd.fderiv

end NLS.FunctionalAnalysis
