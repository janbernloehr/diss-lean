import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Complex differentials are determined by agreement on a spanning real form -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem fderiv_eq_of_real_form_agreement (V : Submodule ℝ E)
    (hspan : ∀ h : E, ∃ x y : V, h = x.val+I • y.val)
    (f g : E → F) (a : V) (hf : DifferentiableAt ℂ f a.val)
    (hg : DifferentiableAt ℂ g a.val) (heq : ∀ b : V, f b.val = g b.val) :
    fderiv ℂ f a.val = fderiv ℂ g a.val := by
  have hd := (hf.hasFDerivAt.restrictScalars ℝ).comp a V.subtypeL.hasFDerivAt
  have he := (hg.hasFDerivAt.restrictScalars ℝ).comp a V.subtypeL.hasFDerivAt
  change HasFDerivAt (fun b : V => f b.val) _ a at hd
  change HasFDerivAt (fun b : V => g b.val) _ a at he
  rw [funext heq] at hd
  have hr (b : V) : fderiv ℂ f a.val b.val = fderiv ℂ g a.val b.val :=
    congrArg (fun L : V →L[ℝ] F => L b) (hd.unique he)
  apply ContinuousLinearMap.ext
  intro h
  obtain ⟨x,y,rfl⟩ := hspan h
  simp only [map_add,map_smul,hr]

end NLS.ComplexAnalysis
