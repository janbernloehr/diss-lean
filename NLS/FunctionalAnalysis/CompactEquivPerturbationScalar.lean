import NLS.FunctionalAnalysis.CompactScalarPerturbation
import Mathlib.Analysis.Complex.Basic

/-! # Actual injective compact perturbations of bounded equivalences -/
noncomputable section
set_option autoImplicit false
namespace NLS

/-- An ACTUAL injective compact perturbation of a bounded equivalence is
bijective. The original operator is retained, without choosing a new inverse. -/
theorem bijective_of_compact_sub_equiv_of_injective_scalar
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : E →L[𝕜] F) (Q : E ≃L[𝕜] F)
    (hc : IsCompactOperator (A-Q.toContinuousLinearMap)) (hi : Function.Injective A) :
    Function.Bijective A := by
  let B := Q.symm.toContinuousLinearMap.comp A
  have hdiff : B-(1 : E →L[𝕜] E)=Q.symm.toContinuousLinearMap.comp (A-Q.toContinuousLinearMap) := by
    ext x
    change Q.symm (A x)-x=Q.symm (A x-Q x)
    rw [map_sub,Q.symm_apply_apply]
  have hcB : IsCompactOperator (B-(1 : E →L[𝕜] E)) := by
    rw [hdiff]
    exact hc.clm_comp Q.symm.toContinuousLinearMap
  have hiB : Function.Injective B := Q.symm.injective.comp hi
  have hbij := CompactScalarPerturbation.bijective_of_injective B (c := (1 : 𝕜)) one_ne_zero (by simpa only [one_smul] using hcB) hiB
  refine ⟨hi,?_⟩
  intro y
  obtain ⟨x,hx⟩ := hbij.surjective (Q.symm y)
  exact ⟨x,Q.symm.injective hx⟩

end NLS
