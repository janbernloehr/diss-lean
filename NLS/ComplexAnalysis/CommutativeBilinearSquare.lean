import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Complex.Basic

/-! # Derivative of a commutative bounded bilinear square -/
noncomputable section
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem hasFDerivAt_commutative_bilinear_square (B : E →L[ℂ] E →L[ℂ] F)
    (hB : ∀ x y, B x y = B y x) (a : E) :
    HasFDerivAt (fun x => B x x) ((2 : ℂ) • B a) a := by
  have hd := B.hasFDerivAt_of_bilinear (hasFDerivAt_id a) (hasFDerivAt_id a)
  convert hd using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro h
    simp only [smul_apply,add_apply,ContinuousLinearMap.precompR_apply,ContinuousLinearMap.precompL_apply,
      ContinuousLinearMap.id_apply,id_eq]
    rw [hB h a,two_smul]
    rfl

end NLS.ComplexAnalysis
