import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerRegularity
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapRegularity
import NLS.SequenceSpaces.SignedSobolevPositiveEquivalence

/-! Every actual rough finite-gap source has a genuine H1 representative
with the same entire coefficient sequence and the same zero mean. -/
noncomputable section
open Set NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hillReal_has_H1_representative_of_mem_sobolev (q : HillRealMeanZeroSource)
    (hq : Memℓp (fun k => (Weight.sobolev (signedStepOrder 0 1) k:ℂ)*
      (hillRealMeanZeroInclusion q).val k) 2) :
    ∃ a : RealSignedHilbert (signedStepOrder 0 1), hillIntegerSourceInclusion 1 a=q := by
  let s := signedStepOrder 0 1
  have hs : 0 ≤ s := by dsimp only [s]; rw [hillIntegerSobolev_source_order]; norm_num
  let b : WeightedCoeff (Weight.sobolev s) 2 :=
    ⟨(hillRealMeanZeroInclusion q).val,hq⟩
  have hw : ∀ k, Weight.signedSobolev s k ≤ 1*Weight.sobolev s k := by
    intro k
    simpa only [one_mul] using Weight.signedSobolev_le_sobolev s hs k
  let v := WeightComparison.map (Weight.sobolev s) (Weight.signedSobolev s) 1 zero_le_one hw b
  have hv (k : ℤ) : v.val k=q.val.val.val k :=
    WeightComparison.map_apply _ _ 1 zero_le_one hw b k
  let a : RealSignedHilbert s := ⟨⟨v,by change v.val 0=0; rw [hv]; exact q.val.property⟩,by
    intro k
    change v.val (-k)=(starRingEnd ℂ) (v.val k)
    rw [hv,hv]
    exact q.property k⟩
  refine ⟨a,?_⟩
  apply hillRealMeanZeroInclusion_injective
  apply Subtype.ext
  funext k
  change (hillIntegerSourceInclusion 1 a).val.val.val k=q.val.val.val k
  rw [hillIntegerSourceInclusion_apply]
  exact hv k

theorem hillRealFiniteGap_has_H1_representative (q : HillRealMeanZeroSource)
    (hf : q ∈ hillRealFiniteGapLocus) :
    ∃ a : RealSignedHilbert (signedStepOrder 0 1), hillIntegerSourceInclusion 1 a=q := by
  exact hillReal_has_H1_representative_of_mem_sobolev q
    (hillRealFiniteGap_mem_all_sobolev q hf _ (by rw [hillIntegerSobolev_source_order]; norm_num))

theorem denseRange_hillIntegerSourceInclusion_one : DenseRange (hillIntegerSourceInclusion 1) := by
  exact dense_hillRealFiniteGapLocus.mono (fun q hq => hillRealFiniteGap_has_H1_representative q hq)

end NLS.Articles.KdVPseudomeasures
