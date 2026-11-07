import NLS.FunctionalAnalysis.CompactDecomposition

/-! Injective compact perturbations of Banach isomorphisms between
possibly DIFFERENT spaces are bounded isomorphisms. -/
noncomputable section
namespace NLS.CompactSpectrum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem bijective_of_injective_compact_difference (e : E ≃L[ℂ] F) (A : E →L[ℂ] F)
    (hc : IsCompactOperator (A-e.toContinuousLinearMap)) (hi : Function.Injective A) :
    Function.Bijective A := by
  let T := e.symm.toContinuousLinearMap.comp A
  have he : T-1=e.symm.toContinuousLinearMap.comp (A-e.toContinuousLinearMap) := by
    ext x
    change e.symm (A x)-x=e.symm (A x-e x)
    rw [map_sub,e.symm_apply_apply]
  have hC : IsCompactOperator (T-(1 : E →L[ℂ] E)) := by
    rw [he]
    exact hc.clm_comp e.symm.toContinuousLinearMap
  have hT := bijective_of_injective_compact_sub_smul T (c := (1:ℂ)) one_ne_zero
    (by simpa only [one_smul] using hC) (e.symm.injective.comp hi)
  refine ⟨hi,?_⟩
  intro y
  obtain ⟨x,hx⟩ := hT.2 (e.symm y)
  exact ⟨x,e.symm.injective hx⟩

def equivOfInjectiveCompactDifference (e : E ≃L[ℂ] F) (A : E →L[ℂ] F)
    (hc : IsCompactOperator (A-e.toContinuousLinearMap)) (hi : Function.Injective A) : E ≃L[ℂ] F :=
  ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr (bijective_of_injective_compact_difference e A hc hi).1)
    (LinearMap.range_eq_top.mpr (bijective_of_injective_compact_difference e A hc hi).2)

end NLS.CompactSpectrum
