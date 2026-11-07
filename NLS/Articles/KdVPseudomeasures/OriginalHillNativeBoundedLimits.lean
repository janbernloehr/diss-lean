import NLS.Articles.KdVPseudomeasures.OriginalHillBoundedActionCompactness
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeInjectivity
import NLS.Articles.KdVPseudomeasures.MainTheorem14WeakStar
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! ACTUAL native output limits of norm-bounded original sources have
original preimages. The remaining native properness/onto obligation is
exactly a bound on preimages of compact target sets; that bound is NOT
assumed established here. -/
noncomputable section
open Set Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem exists_hillReal_preimage_of_bounded_nativeMap_tendsto
    (a : ℕ → HillRealMeanZeroSource) (z : HillRealSignedTarget)
    (hb : Bornology.IsBounded (range a))
    (ht : Tendsto (fun k => hillRealSignedMap (a k)) atTop (𝓝 z)) :
    ∃ q : HillRealMeanZeroSource, hillRealSignedMap q=z := by
  obtain ⟨q,σ,hσ,hI⟩ := exists_hillReal_canonicalAction_subseq_of_bounded a hb
  have hF := ht.comp hσ.tendsto_atTop
  have hz : z ∈ hillRealNativeActionTorus q := by
    intro n
    have hp : Tendsto (fun k => (hillRealSignedMap (a (σ k))).val.val.val (n:ℤ)) atTop
        (𝓝 (z.val.val.val (n:ℤ))) :=
      (WeightedCoeff.fourierRealZeroEvalCLM (Weight.signedSobolev (-1/2)) 2 (n:ℤ)).continuous.continuousAt.tendsto.comp hF
    have hm : Tendsto (fun k => (hillRealSignedMap (a (σ k))).val.val.val (-(n:ℤ))) atTop
        (𝓝 (z.val.val.val (-(n:ℤ)))) :=
      (WeightedCoeff.fourierRealZeroEvalCLM (Weight.signedSobolev (-1/2)) 2 (-(n:ℤ))).continuous.continuousAt.tendsto.comp hF
    have hprod := hp.mul hm
    have he : (fun k => (hillRealSignedMap (a (σ k))).val.val.val (n:ℤ)*
        (hillRealSignedMap (a (σ k))).val.val.val (-(n:ℤ)))=
        (fun k => hillHminusCanonicalAction n (hillRealMeanZeroInclusion (a (σ k)))) := by
      funext k
      exact (hillRealSignedMap_mem_actionTorus_of_discriminant_eq (a (σ k)) (a (σ k)) rfl) n
    rw [he] at hprod
    exact tendsto_nhds_unique hprod (hI n)
  obtain ⟨p,_,hp⟩ := exists_hillReal_isospectral_preimage_of_mem_actionTorus q z hz
  exact ⟨p,hp⟩

theorem exists_hillReal_source_limit_of_bounded_nativeMap_tendsto
    (a : ℕ → HillRealMeanZeroSource) (z : HillRealSignedTarget)
    (hb : Bornology.IsBounded (range a))
    (ht : Tendsto (fun k => hillRealSignedMap (a k)) atTop (𝓝 z)) :
    ∃ q : HillRealMeanZeroSource, hillRealSignedMap q=z ∧ Tendsto a atTop (𝓝 q) := by
  obtain ⟨q,hq⟩ := exists_hillReal_preimage_of_bounded_nativeMap_tendsto a z hb ht
  refine ⟨q,hq,?_⟩
  apply isOpenEmbedding_hillRealSignedMap.tendsto_nhds_iff.mpr
  rw [hq]
  exact ht

theorem isProperMap_hillRealSignedMap_iff_bounded_compact_preimages :
    IsProperMap hillRealSignedMap ↔
      ∀ K : Set HillRealSignedTarget, IsCompact K → Bornology.IsBounded (hillRealSignedMap ⁻¹' K) := by
  constructor
  · intro hp K hK
    exact (hp.isCompact_preimage hK).isBounded
  · intro hb
    apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨hillPhysicalNativeMap_isLocalHomeomorph.continuous,?_⟩
    intro K hK
    apply IsSeqCompact.isCompact
    intro a ha
    have haF : ∀ k, hillRealSignedMap (a k) ∈ K := fun k => Set.mem_preimage.mp (ha k)
    have hba : Bornology.IsBounded (range a) := (hb K hK).subset (by rintro _ ⟨k,rfl⟩; exact ha k)
    obtain ⟨z,hz,σ,hσ,ht⟩ := hK.tendsto_subseq haF
    have hbs : Bornology.IsBounded (range (a ∘ σ)) := hba.subset (range_comp_subset_range _ _)
    obtain ⟨q,hq,htq⟩ := exists_hillReal_source_limit_of_bounded_nativeMap_tendsto (a ∘ σ) z hbs ht
    exact ⟨q,Set.mem_preimage.mpr (hq.symm ▸ hz),σ,hσ,htq⟩

/-- This supplies the FULL precise main statement from a PURE norm-bound
obligation on compact target preimages. The obligation remains explicit. -/
theorem sourceTheorem1_4_of_bounded_compact_native_preimages
    (hb : ∀ K : Set HillRealSignedTarget, IsCompact K → Bornology.IsBounded (hillRealSignedMap ⁻¹' K)) :
    sourceTheorem1_4Statement :=
  sourceTheorem1_4_of_native_isClosedMap
    (isProperMap_hillRealSignedMap_iff_bounded_compact_preimages.mpr hb).isClosedMap

end NLS.Articles.KdVPseudomeasures
