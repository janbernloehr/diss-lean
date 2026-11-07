import NLS.Articles.KdVPseudomeasures.OriginalHillWienerSmoothingReduction
import NLS.SequenceSpaces.SignedSpatialAnalyticMapLadder
import NLS.SequenceSpaces.SignedSobolevOrderInclusion

/-! The actual Wiener problem at ALL integer orders reduces to the
single L2 one-smoothing defect. Spatial covariance is DERIVED from the
actual native map and the exact free Fourier symbol. The base smoothing
estimate remains an explicit premise, not a claimed result. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hillIntegerNativeOneSmoothing_all_of_base (hbase : HillIntegerNativeOneSmoothing 0) :
    ∀ N : ℕ, HillIntegerNativeOneSmoothing N := by
  obtain ⟨R,hRa,hRc⟩ := hbase
  have hcov (a : RealSignedHilbert (signedStepOrder 0 0)) (x : ℝ) :
      R (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x a) =
        fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x (R a) := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    have hleft := hRc (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x a) k
    have hright := hRc a k
    rw [(hillIntegerSobolevEquiv 0).spatial, fourierRealZeroSpatialTranslation_apply,
      fourierRealZeroSpatialTranslation_apply] at hleft
    rw [fourierRealZeroSpatialTranslation_apply]
    calc
      _ = _ := hleft
      _ = exp (((x * (2 * Real.pi * k) : ℝ) : ℂ) * I) *
          (((hillIntegerSobolevEquiv 0).equiv a).val.val.val k - halfFourierSymbol k * a.val.val.val k) := by ring
      _ = _ := congrArg (fun z : ℂ => exp (((x * (2 * Real.pi * k) : ℝ) : ℂ) * I) * z) hright.symm
  intro N
  have horder : signedStepOrder (1/2) N + 1 ≤ signedStepOrder ((1/2 : ℝ) + 1) N := by
    rw [signedStepOrder_eq, signedStepOrder_eq]
    linarith
  let J := signedRealOrderInclusion (p := 2) _ _ horder
  let T := signedAnalyticMapIterate 0 ((1/2 : ℝ) + 1) R N
  refine ⟨fun q => J (T q), ?_, ?_⟩
  · intro q
    have hJ := @ContinuousLinearMap.analyticAt ℝ inferInstance
      (RealSignedHilbert (signedStepOrder ((1/2 : ℝ) + 1) N)) inferInstance inferInstance
      (RealSignedHilbert (signedStepOrder (1/2) N + 1)) inferInstance inferInstance J (T q)
    exact hJ.comp (analyticAt_signedAnalyticMapIterate 0 ((1/2 : ℝ) + 1) R hRa N q)
  · intro q k
    change (J (T q)).val.val.val k = _
    rw [signedRealOrderInclusion_apply, signedAnalyticMapIterate_apply 0 ((1/2 : ℝ) + 1) R hRa hcov]
    have he : ((hillIntegerSobolevEquiv N).equiv q).val.val.val k =
        ((hillIntegerSobolevEquiv 0).equiv (signedIteratedInclusion 0 N q)).val.val.val k :=
      SignedSpatialAnalyticEquiv.iterate_inclusion_apply hillL2SpatialAnalyticEquiv N q k
    calc
      _ = ((hillIntegerSobolevEquiv 0).equiv (signedIteratedInclusion 0 N q)).val.val.val k -
          halfFourierSymbol k * (signedIteratedInclusion 0 N q).val.val.val k := hRc _ k
      _ = ((hillIntegerSobolevEquiv 0).equiv (signedIteratedInclusion 0 N q)).val.val.val k -
          halfFourierSymbol k * q.val.val.val k :=
        congrArg (fun z : ℂ => ((hillIntegerSobolevEquiv 0).equiv
          (signedIteratedInclusion 0 N q)).val.val.val k - halfFourierSymbol k * z)
          (signedIteratedInclusion_apply 0 N q k)
      _ = _ := congrArg (fun z : ℂ => z - halfFourierSymbol k * q.val.val.val k) he.symm

theorem hillWienerBirkhoffDiffeomorphism_all_of_baseSmoothing
    (hbase : HillIntegerNativeOneSmoothing 0) : ∀ N : ℕ, HillWienerBirkhoffDiffeomorphism N :=
  fun N => hillWienerBirkhoffDiffeomorphism_of_oneSmoothing N
    (hillIntegerNativeOneSmoothing_all_of_base hbase N)

end NLS.Articles.KdVPseudomeasures
