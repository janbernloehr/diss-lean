import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerRegularity
import NLS.KdV.HillNativeFiniteGap
import NLS.Topology.DensePreimageApproximation

/-! Genuine finite-gap approximation in EVERY nonnegative integer
Sobolev norm, using the SAME actual native map and its proved global inverse. -/
noncomputable section
open Set Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

def hillIntegerFiniteGapApproximation (s : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 s)) (N : ℕ) :
    RealSignedHilbert (signedStepOrder 0 s) :=
  (hillIntegerSobolevEquiv s).equiv.symm (fourierRealZeroTruncate
    (Weight.signedSobolev (signedStepOrder (1/2) s)) N ((hillIntegerSobolevEquiv s).equiv q))

theorem hillIntegerFiniteGapApproximation_tendsto (s : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 s)) :
    Tendsto (hillIntegerFiniteGapApproximation s q) atTop (𝓝 q) := by
  have ht := tendsto_fourierRealZeroTruncate (p:=2) (by simp)
    (Weight.signedSobolev (signedStepOrder (1/2) s)) ((hillIntegerSobolevEquiv s).equiv q)
  have h := ((hillIntegerSobolevEquiv s).analytic_symm _).continuousAt.tendsto.comp ht
  simpa only [hillIntegerFiniteGapApproximation,(hillIntegerSobolevEquiv s).equiv.symm_apply_apply] using! h

theorem hillIntegerFiniteGapApproximation_native (s : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 s)) (N : ℕ) :
    hillRealSignedMap (hillIntegerSourceInclusion s (hillIntegerFiniteGapApproximation s q N))=
      hillIntegerTargetInclusion s (fourierRealZeroTruncate
        (Weight.signedSobolev (signedStepOrder (1/2) s)) N ((hillIntegerSobolevEquiv s).equiv q)) := by
  rw [← hillIntegerSobolevEquiv_inclusion]
  exact congrArg (hillIntegerTargetInclusion s) ((hillIntegerSobolevEquiv s).equiv.apply_symm_apply _)

theorem hillIntegerFiniteGapApproximation_mem (s : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 s)) (N : ℕ) :
    hillIntegerSourceInclusion s (hillIntegerFiniteGapApproximation s q N) ∈ hillRealFiniteGapLocus := by
  refine ⟨N,fun n hn => ?_⟩
  apply (hillRealSignedMap_positive_eq_zero_iff_gapSquare _ n).mp
  rw [hillIntegerFiniteGapApproximation_native,hillIntegerTargetInclusion_apply,
    fourierRealZeroTruncate_apply,Int.natAbs_natCast,if_neg (by omega)]

theorem dense_hillIntegerFiniteGapLocus (s : ℕ) :
    Dense (hillIntegerSourceInclusion s ⁻¹' hillRealFiniteGapLocus) := by
  apply NLS.Topology.dense_preimage_of_approximating_sequences
  intro q
  exact ⟨hillIntegerFiniteGapApproximation s q,hillIntegerFiniteGapApproximation_tendsto s q,
    Filter.Eventually.of_forall (hillIntegerFiniteGapApproximation_mem s q)⟩

end NLS.Articles.KdVPseudomeasures
