import NLS.FunctionalAnalysis.CompactDenseRange
import NLS.FunctionalAnalysis.CompactEquivPerturbation

/-! # Dense-range compact perturbations of actual bounded equivalences -/
noncomputable section
set_option autoImplicit false
namespace NLS

/-- The actual dense-range compact perturbation of a bounded equivalence
is bijective. No injectivity or surjectivity premise is supplied. -/
theorem bijective_of_compact_sub_equiv_of_denseRange
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : E →L[ℂ] F) (Q : E ≃L[ℂ] F)
    (hc : IsCompactOperator (A-Q.toContinuousLinearMap)) (hd : DenseRange A) :
    Function.Bijective A := by
  let B := Q.symm.toContinuousLinearMap.comp A
  have he : B-(1 : E →L[ℂ] E) = Q.symm.toContinuousLinearMap.comp (A-Q.toContinuousLinearMap) := by
    ext x
    change Q.symm (A x)-x = Q.symm (A x-Q x)
    rw [map_sub,Q.symm_apply_apply]
  have hcB : IsCompactOperator (B-(1 : E →L[ℂ] E)) := by
    rw [he]
    exact hc.clm_comp Q.symm.toContinuousLinearMap
  have hdB : DenseRange B := Q.symm.surjective.denseRange.comp hd Q.symm.continuous
  have hb := CompactSpectrum.bijective_of_denseRange_compact_sub_id B hcB hdB
  refine ⟨fun x y h => hb.injective (congrArg Q.symm h),?_⟩
  intro y
  obtain ⟨x,hx⟩ := hb.surjective (Q.symm y)
  exact ⟨x,Q.symm.injective hx⟩

end NLS
