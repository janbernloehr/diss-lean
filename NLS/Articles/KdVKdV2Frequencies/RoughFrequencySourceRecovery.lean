import NLS.Articles.KdVKdV2Frequencies.NativeActionNormalization
import NLS.Articles.KdVKdV2Frequencies.GlobalWeakFrequencyNormalization

/-! The ONE weak-action frequency is the actual physical correction
at every real rough mean-zero source and in every compatible Miura chart. -/
noncomputable section
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem roughWeakActionCoordinates_of_signed_inverse
    (D : GlobalRoughAbelianForwardData) (q : PeriodOneHminusOne) (hqm : q.val 0=0)
    (z : Coeff 2 × Coeff 2)
    (hi : D.signed q=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))
      (signedPairToDeleted actionIndexEquiv z)) :
    roughWeakActionCoordinates D q=quadraticActionsExponent (q := 1) z := by
  unfold roughWeakActionCoordinates
  change quadraticActionsExponent (q := 1) (deletedToSignedPair actionIndexEquiv
    (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
      (D.signed (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
        (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)) q)))))=_
  rw [WeightedCoeff.meanZeroWeightedLift_projection _ q hqm,hi,
    WeightedCoeff.meanZeroWeightedProjection_lift]
  ext k
  rw [quadraticActions_deletedToSignedPair_apply,signedPairToDeleted_product]

theorem roughKdVFrequencyCorrection_eq_physical
    (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n,
        G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (B : PhysicalMiuraFrequencyChart) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0=0) (hqB : q∈B.domain) (n : ℕ+) :
    roughKdVFrequencyCorrection D G n q=B.correction n q := by
  obtain ⟨z,hzr,U,hU,hzU,Q,hQ,hQz,hd⟩ := exists_hillRough_pair_inverse D actionIndexEquiv q hr hm
  let V := U∩Q ⁻¹' B.domain
  let P : PhysicalFrequencyPairChart D :=
    ⟨V,hQ.continuousOn.isOpen_inter_preimage hU B.domain_open,Q,hQ.mono inter_subset_left,
      (fun w hw => (hd w hw.1).1),(fun w hw => (hd w hw.1).2.1),
      (fun w hw hwr => (hd w hw.1).2.2 hwr),B,(fun _ hw => hw.2)⟩
  have hzV : z∈V := ⟨hzU,by change Q z∈B.domain;rwa [hQz]⟩
  have hi : D.signed q=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))
      (signedPairToDeleted actionIndexEquiv z) := by
    rw [← hQz]
    exact (hd z hzU).2.1
  rw [roughKdVFrequencyCorrection,roughWeakActionCoordinates_of_signed_inverse D q hm z hi]
  have h := hrec P z hzV hzr n
  change _=B.correction n (Q z) at h
  rwa [hQz] at h

theorem roughKdVFrequency_native_recovery
    (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n,
        G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) (n : ℕ+) :
    roughKdVFrequency D G n (nativeHillSource 1 q.val)=(D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n:ℂ) := by
  have hr := nativeHillSource_real 1 q.val q.property.1
  have hm : (nativeHillSource 1 q.val).val 0=0 := (nativeHillSource_apply 1 q.val 0).trans q.property.2
  obtain ⟨B,hqB,_⟩ := exists_physicalMiuraFrequencyChart (nativeHillSource 1 q.val) hr 0
  have hs : hillOriginalHminusSource (nativeHillPhysicalSource 1 q.val q.property.1).val=nativeHillSource 1 q.val := by
    rw [hillOriginalHminusSource_eq_physical]
    exact (nativeHillSource_eq_physical 1 q.val q.property.1).symm
  have hN := native_physical_frequency_eq_miura_chart D B q (by rwa [hs]) n
  rw [hs] at hN
  rw [roughKdVFrequency,roughKdVFrequencyCorrection_eq_physical D G hrec B _ hr hm hqB n,← hN]
  ring

end NLS.Articles.KdVKdV2Frequencies
