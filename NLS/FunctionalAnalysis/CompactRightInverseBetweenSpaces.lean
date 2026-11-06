import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Complex.Basic

/-! # Compact remainders of actual right inverses between different spaces -/
noncomputable section
set_option autoImplicit false
namespace NLS

/-- A right inverse of a compact perturbation of a bounded equivalence
differs compactly from the inverse equivalence. The actual map need not
be assumed injective, and its right inverse need not be chosen afresh. -/
theorem isCompactOperator_rightInverse_sub_equiv_symm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : E →L[ℂ] F) (B : F →L[ℂ] E) (Q : E ≃L[ℂ] F)
    (hA : IsCompactOperator (A-Q.toContinuousLinearMap))
    (hAB : A.comp B=ContinuousLinearMap.id ℂ F) :
    IsCompactOperator (B-Q.symm.toContinuousLinearMap) := by
  have he : B-Q.symm.toContinuousLinearMap=
      -(Q.symm.toContinuousLinearMap.comp ((A-Q.toContinuousLinearMap).comp B)) := by
    ext x
    have hx := congrArg (fun L => L x) hAB
    change A (B x)=x at hx
    change B x-Q.symm x= -Q.symm (A (B x)-Q (B x))
    rw [map_sub,hx,Q.symm_apply_apply]
    abel
  rw [he]
  exact ((hA.comp_clm B).clm_comp Q.symm.toContinuousLinearMap).neg

end NLS
