import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! # Injectivity of actual derivatives through fixed inclusion diagrams -/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.ComplexAnalysis
variable {E F H K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

theorem fderiv_injective_of_differentiable_leftInverse
    (f : E → F) (g : F → E) (a : E) (hf : DifferentiableAt ℝ f a)
    (hg : DifferentiableAt ℝ g (f a)) (hleft : Function.LeftInverse g f) :
    Function.Injective (fderiv ℝ f a) := by
  have hh := hg.hasFDerivAt.comp a hf.hasFDerivAt
  have he : (fun x => g (f x))=id := funext hleft
  change HasFDerivAt (fun x => g (f x)) _ a at hh
  rw [he] at hh
  have hd := hh.unique (hasFDerivAt_id a)
  intro x y hxy
  have hx := congrArg (fun L : E →L[ℝ] E => L x) hd
  have hy := congrArg (fun L : E →L[ℝ] E => L y) hd
  change fderiv ℝ g (f a) (fderiv ℝ f a x)=x at hx
  change fderiv ℝ g (f a) (fderiv ℝ f a y)=y at hy
  exact hx.symm.trans ((congrArg (fderiv ℝ g (f a)) hxy).trans hy)

theorem fderiv_injective_of_linear_intertwining
    (f : E → F) (g : H → K) (L : E →L[ℝ] H) (M : F →L[ℝ] K) (a : E)
    (hf : DifferentiableAt ℝ f a) (hg : DifferentiableAt ℝ g (L a))
    (hcomm : ∀ x, M (f x)=g (L x)) (hL : Function.Injective L)
    (hginj : Function.Injective (fderiv ℝ g (L a))) :
    Function.Injective (fderiv ℝ f a) := by
  have h1 := M.hasFDerivAt.comp a hf.hasFDerivAt
  have h2 := hg.hasFDerivAt.comp a L.hasFDerivAt
  have he : (fun x => M (f x))=(fun x => g (L x)) := funext hcomm
  change HasFDerivAt (fun x => M (f x)) _ a at h1
  rw [he] at h1
  have hd := h1.unique h2
  intro x y hxy
  apply hL
  apply hginj
  change ((fderiv ℝ g (L a)).comp L) x=((fderiv ℝ g (L a)).comp L) y
  rw [←hd]
  change M (fderiv ℝ f a x)=M (fderiv ℝ f a y)
  rw [hxy]

end NLS.ComplexAnalysis
