import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Scalar restriction of a continuous complex linear equivalence between
DIFFERENT spaces. Both the forward and inverse maps are retained exactly. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℂ E] [NormedSpace ℂ F] [NormedSpace ℝ E] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]

def complexEquivRealRestriction (e : E ≃L[ℂ] F) : E ≃L[ℝ] F where
  toLinearEquiv :=
    { toLinearMap := (e.toContinuousLinearMap.restrictScalars ℝ).toLinearMap
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }
  continuous_toFun := e.continuous
  continuous_invFun := e.symm.continuous

theorem complexEquivRealRestriction_apply (e : E ≃L[ℂ] F) (a : E) :
    complexEquivRealRestriction e a=e a := rfl

theorem complexEquivRealRestriction_symm_apply (e : E ≃L[ℂ] F) (a : F) :
    (complexEquivRealRestriction e).symm a=e.symm a := rfl

end NLS.FunctionalAnalysis
