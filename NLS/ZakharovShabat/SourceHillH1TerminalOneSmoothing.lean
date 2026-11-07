import NLS.ZakharovShabat.SourceSignedTerminalH1Realization
import NLS.ZakharovShabat.SourceNormalizedMidpointOneSmoothing
import NLS.ZakharovShabat.SourceHillWeightedTerminalModel
import NLS.SequenceSpaces.SobolevHilbertPointwiseProduct
import NLS.SequenceSpaces.SobolevToSignedHalfLift

/-! The actual native Hill terminal model minus its exact signed
Fourier principal part is analytic from H1 to native signed H3/2.
Both the literal terminal defect and the differentiated midpoint
factor are retained; the conclusion is a norm smoothing assertion. -/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

def sourceHillH1TerminalRemainder (a : ScalarDomain 2 × ScalarDomain 2) :
    WeightedCoeff (Weight.signedSobolev (3/2)) 2 :=
  sourceHillTerminalScale • WeightedCoeff.sobolevToSignedHalfLift (1+1) (3/2)
    (by norm_num) (by norm_num) 2
      (sourceSignedTerminalH2Remainder a + WeightedCoeff.sobolevHilbertPointwiseProduct 1 1
        (sourceNormalizedMidpointSobolevRemainder (sobolevSourceInclusion a))
        (sourceSignedTerminalH1Sequence a))

private theorem terminal_remainder_raw (a : ScalarDomain 2 × ScalarDomain 2) (k : ℤ)
    (hR : (sourceSignedTerminalH2Remainder a).val k =
      sourceSignedTerminalSequence (sobolevSourceInclusion a) k -
        sourceSignedTerminalFourier (sobolevSourceInclusion a) k)
    (hT : (sourceSignedTerminalH1Sequence a).val k =
      sourceSignedTerminalSequence (sobolevSourceInclusion a) k)
    (hA : (sourceNormalizedMidpointSobolevRemainder (sobolevSourceInclusion a)).val k =
      sourceNormalizedMidpointSymbol (by simp) (by norm_num) (sobolevSourceInclusion a) k - 1) :
    (sourceHillH1TerminalRemainder a).val k =
      (sourceHillTerminalModel (sobolevSourceInclusion a)).val k -
        (sourceHillTerminalFourier (sobolevSourceInclusion a)).val k := by
  let w := (Weight.signedSobolev (-1/2) k : ℂ)
  have hw : w ≠ 0 := (Weight.signedSobolev (-1/2)).complex_ne_zero k
  have hm := sourceHillTerminalModel_weighted_apply (sobolevSourceInclusion a) k
  have hf := sourceHillTerminalFourier_weighted_apply (sobolevSourceInclusion a) k
  change w * (sourceHillTerminalModel (sobolevSourceInclusion a)).val k = _ at hm
  change w * (sourceHillTerminalFourier (sobolevSourceInclusion a)).val k = _ at hf
  apply mul_left_cancel₀ hw
  rw [mul_sub, hm, hf]
  simp only [sourceHillH1TerminalRemainder, WeightedCoeff.smul_val,
    WeightedCoeff.sobolevToSignedHalfLift_apply, WeightedCoeff.add_val,
    WeightedCoeff.sobolevHilbertPointwiseProduct_apply, hR, hT, hA]
  change w * (sourceHillTerminalScale * (w⁻¹ * _)) = _
  field_simp; ring

theorem exists_local_sourceHillH1TerminalRemainder_analytic (a : realTypeSobolevSourceLocus) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a.val ∈ U ∧
      AnalyticOnNhd ℂ sourceHillH1TerminalRemainder U ∧
      ∀ b ∈ U, ∀ k : ℤ, (sourceHillH1TerminalRemainder b).val k =
        (sourceHillTerminalModel (sobolevSourceInclusion b)).val k -
          (sourceHillTerminalFourier (sobolevSourceInclusion b)).val k := by
  obtain ⟨V,hV,haV,hR,hT,hraw⟩ := exists_local_sourceSignedTerminal_H1_H2_realization a
  obtain ⟨W,hW,hreal,hA,hAc⟩ := exists_sourceNormalizedMidpoint_one_smoothing_domain
  let U := V ∩ sobolevSourceInclusion ⁻¹' W
  have hU : IsOpen U := hV.inter (hW.preimage sobolevSourceInclusion.continuous)
  refine ⟨U,hU,⟨haV,hreal a.property⟩,?_,?_⟩
  · intro b hb
    have ha : AnalyticAt ℂ (fun c : ScalarDomain 2 × ScalarDomain 2 =>
        sourceNormalizedMidpointSobolevRemainder (sobolevSourceInclusion c)) b :=
      (hA _ hb.2).comp (sobolevSourceInclusion.analyticAt b)
    have hp : AnalyticAt ℂ (fun c : ScalarDomain 2 × ScalarDomain 2 =>
        WeightedCoeff.sobolevHilbertPointwiseProduct 1 1
          (sourceNormalizedMidpointSobolevRemainder (sobolevSourceInclusion c))
          (sourceSignedTerminalH1Sequence c)) b :=
      (WeightedCoeff.analyticAt_sobolevHilbertPointwiseProduct 1 1 _).comp
        (f := fun c : ScalarDomain 2 × ScalarDomain 2 =>
          (sourceNormalizedMidpointSobolevRemainder (sobolevSourceInclusion c),
            sourceSignedTerminalH1Sequence c)) (ha.prod (hT b hb.1))
    exact (((WeightedCoeff.sobolevToSignedHalfLift (1+1) (3/2)
      (by norm_num) (by norm_num) 2).analyticAt _).comp ((hR b hb.1).add hp)).const_smul
        (c := sourceHillTerminalScale)
  · intro b hb k
    exact terminal_remainder_raw b k (hraw b hb.1 k).1 (hraw b hb.1 k).2 (hAc _ hb.2 k)

end NLS.ZakharovShabat
