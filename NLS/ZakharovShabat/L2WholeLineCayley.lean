import NLS.FunctionalAnalysis.SelfAdjointCayley
import NLS.ZakharovShabat.L2WholeLineNonrealResolvent

/-! # The unitary Cayley transform of the original whole-line operator -/
noncomputable section
set_option autoImplicit false
open Complex NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The actual physical Cayley transform, formed from the verified closure resolvent. -/
def wholeLineCayley (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) : WholeLineL2 →L[ℂ] WholeLineL2 :=
  selfAdjointCayley (wholeLineMinimalOperator_closure_isSelfAdjoint u hu)

theorem wholeLineCayley_eq (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    wholeLineCayley u hu = 1+(2*I) • wholeLineNonrealResolvent u hu (-I) (by simp) := rfl

/-- Both unitary identities hold for the original whole-line Cayley transform. -/
theorem wholeLineCayley_mem_unitary (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    wholeLineCayley u hu ∈ unitary (WholeLineL2 →L[ℂ] WholeLineL2) :=
  selfAdjointCayley_mem_unitary _

/-- The physical Cayley transform has no nonzero fixed vector. -/
theorem wholeLineCayley_apply_eq_self_iff (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (f : WholeLineL2) :
    wholeLineCayley u hu f = f ↔ f = 0 := selfAdjointCayley_apply_eq_self_iff _ f

/-- The actual bounded physical Cayley operator is star-normal. -/
theorem wholeLineCayley_isStarNormal (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) : IsStarNormal (wholeLineCayley u hu) :=
  isStarNormal_of_mem_unitary (wholeLineCayley_mem_unitary u hu)

end NLS.ZakharovShabat
