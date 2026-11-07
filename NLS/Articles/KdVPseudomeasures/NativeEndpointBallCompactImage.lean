import NLS.Articles.KdVPseudomeasures.NativeEndpointRealSignedMap
import NLS.SequenceSpaces.EndpointCompactInclusion
import NLS.KdV.HillDirichletSpectralLocalFlow

/-! Every physical real endpoint norm ball has a norm-compact real
mean-zero envelope in the actual native Hminus-one source. The full
endpoint infinity space is retained. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

/-- A compact native real envelope, obtained by the actual bounded real projection. -/
def endpointRealBallNativeEnvelope (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) : Set PeriodOneHminusOne :=
  (fun a => hillRealMeanZeroInclusion (hillRealMeanZeroProjection a)) ''
    ((endpointNativeInclusion r hr) '' closedBall 0 R)

theorem isCompact_endpointRealBallNativeEnvelope (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    IsCompact (endpointRealBallNativeEnvelope r hr R) := by
  have hc : IsCompact ((endpointNativeInclusion r hr) '' closedBall 0 R) := by
    rw [endpointNativeInclusion_eq_lowerInclusion]
    exact WeightedCoeff.isCompact_endpointLowerInclusion_closedBall r (-1) R (by simp)
      (admissible_hminusOne_threshold r hr)
  exact hc.image (hillRealMeanZeroInclusion.continuous.comp hillRealMeanZeroProjection.continuous)

theorem endpointRealBallNativeEnvelope_real (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ)
    (a : PeriodOneHminusOne) (ha : a ∈ endpointRealBallNativeEnvelope r hr R) :
    IsRealPeriodOneHminusOne a := by
  obtain ⟨b,_,rfl⟩ := ha
  exact (hillRealMeanZeroProjection b).property

theorem endpointNativeInclusion_mem_realBallEnvelope (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (q : HillEndpointRealMeanZeroSource r) (hq : ‖q‖ ≤ R) :
    endpointNativeInclusion r hr q.val.val ∈ endpointRealBallNativeEnvelope r hr R := by
  refine ⟨endpointNativeInclusion r hr q.val.val,⟨q.val.val,?_,rfl⟩,?_⟩
  · rw [mem_closedBall,dist_zero_right]
    change ‖q.val.val‖ ≤ R at hq
    exact hq
  · exact hillRealMeanZeroProjection_inclusion _ (endpointNativeInclusion_real_source r hr q) (by
      rw [endpointNativeInclusion_apply]
      exact q.val.property)

end NLS.Articles.KdVPseudomeasures
