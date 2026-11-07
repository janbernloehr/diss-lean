import NLS.FunctionalAnalysis.CompactDecomposition

/-! The Fredholm alternative for compact perturbations of any given
Banach isomorphism. Kernel injectivity remains an explicit premise. -/
noncomputable section
namespace NLS.CompactSpectrum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem bijective_of_injective_compact_sub_equiv (A : E →L[ℂ] E) (e : E ≃L[ℂ] E)
    (hcompact : IsCompactOperator (A-e.toContinuousLinearMap)) (hinj : Function.Injective A) :
    Function.Bijective A := by
  let B := e.symm.toContinuousLinearMap.comp A
  have he : B-(1:E →L[ℂ] E) = e.symm.toContinuousLinearMap.comp (A-e.toContinuousLinearMap) := by
    ext x
    change e.symm (A x)-x = e.symm (A x-e x)
    rw [map_sub,e.symm_apply_apply]
  have hc : IsCompactOperator (B-(1:E →L[ℂ] E)) := by
    rw [he]
    exact hcompact.clm_comp e.symm.toContinuousLinearMap
  have hbinj : Function.Injective B := e.symm.injective.comp hinj
  have hbij := bijective_of_injective_compact_sub_smul B (c := (1:ℂ)) one_ne_zero (by simpa only [one_smul] using hc) hbinj
  have heq : (fun x => e (B x)) = A := by
    funext x
    exact e.apply_symm_apply (A x)
  rw [← heq]
  exact e.bijective.comp hbij

end NLS.CompactSpectrum
