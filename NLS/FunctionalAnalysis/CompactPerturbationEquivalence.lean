import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-! # Injective compact perturbations of a Banach equivalence

The Fredholm alternative applies after normalization by a bounded
equivalence, including when the two Banach spaces are different.
-/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem bijective_id_sub_compact_of_injective
    (T : E →L[𝕜] E) (hT : IsCompactOperator T)
    (hinj : Function.Injective ((1 : E →L[𝕜] E)-T)) :
    Function.Bijective ((1 : E →L[𝕜] E)-T) := by
  have hnot : ¬ Module.End.HasEigenvalue (T : Module.End 𝕜 E) 1 := by
    intro he
    obtain ⟨v,hv⟩ := he.exists_hasEigenvector
    have hTv : T v = v := by simpa using hv.apply_eq_smul
    have hz : ((1 : E →L[𝕜] E)-T) v = 0 := by simp [hTv]
    exact hv.2 (hinj (by simpa using hz))
  have hr := (hT.hasEigenvalue_or_mem_resolventSet (by norm_num : (1 : 𝕜) ≠ 0)).resolve_left hnot
  have hu : IsUnit ((1 : E →L[𝕜] E)-T) := by
    simpa using spectrum.mem_resolventSet_iff.mp hr
  exact ContinuousLinearMap.isUnit_iff_bijective.mp hu

theorem bijective_of_injective_of_compact_sub_equiv
    (L : E ≃L[𝕜] F) (T : E →L[𝕜] F)
    (hcompact : IsCompactOperator (T-L.toContinuousLinearMap))
    (hinj : Function.Injective T) : Function.Bijective T := by
  let K := -(L.symm.toContinuousLinearMap.comp (T-L.toContinuousLinearMap))
  have hK : IsCompactOperator K := (hcompact.clm_comp L.symm.toContinuousLinearMap).neg
  have he : (1 : E →L[𝕜] E)-K = L.symm.toContinuousLinearMap.comp T := by
    apply ContinuousLinearMap.ext
    intro x
    change x - -(L.symm (T x-L x)) = L.symm (T x)
    rw [map_sub,L.symm_apply_apply]
    abel
  have hN : Function.Injective ((1 : E →L[𝕜] E)-K) := by
    rw [he]
    exact L.symm.injective.comp hinj
  have hb := bijective_id_sub_compact_of_injective K hK hN
  rw [he] at hb
  refine ⟨hinj,fun y => ?_⟩
  obtain ⟨x,hx⟩ := hb.2 (L.symm y)
  exact ⟨x,L.symm.injective hx⟩

theorem exists_equiv_of_injective_of_compact_sub_equiv [CompleteSpace F]
    (L : E ≃L[𝕜] F) (T : E →L[𝕜] F)
    (hcompact : IsCompactOperator (T-L.toContinuousLinearMap))
    (hinj : Function.Injective T) :
    ∃ A : E ≃L[𝕜] F, A.toContinuousLinearMap = T := by
  have hb := bijective_of_injective_of_compact_sub_equiv L T hcompact hinj
  exact ⟨ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2),rfl⟩

end NLS.FunctionalAnalysis
