import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Complex.Basic

/-! # Preservation of an unchanged scalar component under Banach equivalences -/
noncomputable section
namespace NLS.ComplexAnalysis
variable {E A B C : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup C] [NormedSpace ℂ C]

theorem prodCongr_refl_symm_snd (L : B ≃L[ℂ] C) (z : C × ℂ) :
    ((L.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)).symm z).2 = z.2 := rfl

theorem trans_prodCongr_refl_symm_snd
    (S : E ≃L[ℂ] A) (F : A ≃L[ℂ] (C × ℂ)) (L : B ≃L[ℂ] C) (a : E) :
    (((S.trans F).trans (L.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)).symm) a).2 = (F (S a)).2 := rfl

end NLS.ComplexAnalysis
