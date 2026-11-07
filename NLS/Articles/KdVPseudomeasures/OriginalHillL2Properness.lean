import NLS.Articles.KdVPseudomeasures.OriginalHillL2Compactness
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! Properness of the ACTUAL original L2-to-positive-half KdV map.
The exact momentum trace gives bounded sources and prevents norm loss;
native Hminus continuity identifies the genuine coefficient limit. -/
noncomputable section
open Set Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem isProperMap_hillL2NativeMap : IsProperMap hillL2NativeMap := by
  have hcont : Continuous hillL2NativeMap :=
    continuous_iff_continuousAt.mpr (fun u => (analyticAt_hillL2NativeMap u).continuousAt)
  have hnative : Continuous hillRealSignedMap :=
    continuous_iff_continuousAt.mpr (fun q => (analyticAt_hillRealSignedMap q).continuousAt)
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hcont,?_⟩
  intro K hK
  apply IsSeqCompact.isCompact
  intro a ha
  have haF : ∀ k, hillL2NativeMap (a k) ∈ K := fun k => Set.mem_preimage.mp (ha k)
  have hbF : Bornology.IsBounded (range (fun k => hillL2NativeMap (a k))) :=
    hK.isBounded.subset (by rintro _ ⟨k,rfl⟩; exact haF k)
  have hba := hillL2_source_bounded_of_nativeMap_bounded a hbF
  obtain ⟨z,hzK,σ,hσ,hFσ⟩ := hK.tendsto_subseq haF
  have hbσ : Bornology.IsBounded (range (a ∘ σ)) :=
    hba.subset (range_comp_subset_range _ _)
  obtain ⟨b,τ,hτ,ht⟩ := WeightedCoeff.exists_fourierRealZero_coefficientwise_subseq
    (Weight.signedSobolev 0) (a ∘ σ) hbσ
  have hbγ : Bornology.IsBounded (range (a ∘ (σ ∘ τ))) :=
    hba.subset (range_comp_subset_range _ _)
  have hF : Tendsto (fun k => hillL2NativeMap (a ((σ ∘ τ) k))) atTop (𝓝 z) :=
    hFσ.comp hτ.tendsto_atTop
  have hS := tendsto_hillL2SourceInclusion_of_bounded_coefficients (a ∘ (σ ∘ τ)) b hbγ ht
  have hN : Tendsto (fun k => hillRealSignedMap (hillL2SourceInclusion (a ((σ ∘ τ) k)))) atTop
      (𝓝 (hillRealSignedMap (hillL2SourceInclusion b))) := hnative.continuousAt.tendsto.comp hS
  have hT : Tendsto (fun k => hillSignedHalfInclusion (hillL2NativeMap (a ((σ ∘ τ) k)))) atTop
      (𝓝 (hillSignedHalfInclusion z)) := hillSignedHalfInclusion.continuous.continuousAt.tendsto.comp hF
  have he : hillL2NativeMap b=z := by
    apply hillSignedHalfInclusion_injective
    rw [hillL2NativeMap_inclusion]
    simp_rw [hillL2NativeMap_inclusion] at hT
    exact tendsto_nhds_unique hN hT
  have hstrong : Tendsto (a ∘ (σ ∘ τ)) atTop (𝓝 b) :=
    tendsto_hillL2_of_coefficients_of_nativeMap _ b ht (he.symm ▸ hF)
  exact ⟨b,(Set.mem_preimage.mpr (he.symm ▸ hzK)),σ ∘ τ,hσ.comp hτ,hstrong⟩

theorem isClosedMap_hillL2NativeMap : IsClosedMap hillL2NativeMap :=
  isProperMap_hillL2NativeMap.isClosedMap

end NLS.Articles.KdVPseudomeasures
