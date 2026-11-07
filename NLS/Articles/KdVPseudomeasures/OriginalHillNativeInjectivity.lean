import NLS.Articles.KdVPseudomeasures.OriginalHillL2GlobalInverse
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapRegularity

/-! Global injectivity of the ACTUAL full native Hminus KdV map follows
from the now-proved genuine L2 bijection and the verified finite-gap
collision reduction. No native surjectivity or closedness is assumed. -/
noncomputable section
open Set Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem exists_hillL2Source_representative_of_mem_L2Locus
    (q : HillRealMeanZeroSource) (hq : q ∈ hillRealL2Locus) :
    ∃ u : HillRealL2BanachSource, hillL2SourceInclusion u=q := by
  have hm : Memℓp (hillRealMeanZeroInclusion q).val 2 := Set.mem_ofPred_eq.mp hq
  let a : Coeff 2 := ⟨(hillRealMeanZeroInclusion q).val,hm⟩
  obtain ⟨v,hv⟩ := exists_hillRealSpatialGenerator_of_L2 q a (fun _ => rfl)
  exact ⟨hillL2SourceSpatialRecovery v,hillL2SourceInclusion_recovery_eq q v hv⟩

theorem hillRealSignedMap_injOn_L2 : InjOn hillRealSignedMap hillRealL2Locus := by
  intro q hq p hp he
  obtain ⟨u,hu⟩ := exists_hillL2Source_representative_of_mem_L2Locus q hq
  obtain ⟨v,hv⟩ := exists_hillL2Source_representative_of_mem_L2Locus p hp
  have hF : hillL2NativeMap u=hillL2NativeMap v := by
    apply hillSignedHalfInclusion_injective
    rw [hillL2NativeMap_inclusion,hillL2NativeMap_inclusion,hu,hv]
    exact he
  have huv := bijective_hillL2NativeMap.1 hF
  exact hu.symm.trans ((congrArg hillL2SourceInclusion huv).trans hv)

/-- The SAME full actual native output determines every original physical
mean-zero Hminus potential uniquely, including all infinite-gap sources. -/
theorem injective_hillRealSignedMap : Function.Injective hillRealSignedMap :=
  hillPhysicalNative_injective_iff_injOn_L2.mpr hillRealSignedMap_injOn_L2

/-- The full native map is an open embedding in its original norms.
Its image is not asserted to be the whole target here. -/
theorem isOpenEmbedding_hillRealSignedMap : IsOpenEmbedding hillRealSignedMap :=
  hillPhysicalNativeMap_isLocalHomeomorph.isOpenEmbedding_of_injective injective_hillRealSignedMap

end NLS.Articles.KdVPseudomeasures
