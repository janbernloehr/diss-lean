import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! # Restriction of a complex Banach equivalence to real scalars

The source and target may be different spaces. This extends the
endomorphism-only `ContinuousLinearEquiv.restrictScalars` interface. -/
noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Forget complex scalar multiplication, preserving both continuous inverse maps. -/
def complexRealEquiv (e : E ≃L[ℂ] F) : E ≃L[ℝ] F :=
  ContinuousLinearEquiv.equivOfInverse
    (e.toContinuousLinearMap.restrictScalars ℝ)
    (e.symm.toContinuousLinearMap.restrictScalars ℝ)
    e.symm_apply_apply e.apply_symm_apply

@[simp] theorem complexRealEquiv_apply (e : E ≃L[ℂ] F) (x : E) :
    complexRealEquiv e x = e x := rfl

@[simp] theorem complexRealEquiv_symm_apply (e : E ≃L[ℂ] F) (y : F) :
    (complexRealEquiv e).symm y = e.symm y := rfl
end NLS.FunctionalAnalysis
