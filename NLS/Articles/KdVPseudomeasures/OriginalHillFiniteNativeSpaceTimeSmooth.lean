import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalSpatialSynthesis
import NLS.SequenceSpaces.FinitePhaseSpaceTimeSmooth

/-! Joint classical space-time smoothness for the SAME canonical
solution from finite native data. Finite native space-time rotations
pass through the ACTUAL strong analytic inverse. Spatial covariance
identifies evaluation at zero with the original physical field. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff NLS.Fourier NLS.ZakharovShabat NLS.LpSequence
open scoped ContDiff
namespace NLS.Articles.KdVPseudomeasures

theorem contDiff_hillFiniteNative_H1_space_time
    (q : RealSignedHilbert (signedStepOrder 0 1)) (S : Finset ℤ)
    (hq : ∀ k ∉ S, ((hillIntegerSobolevEquiv 1).equiv q).val.val.val k = 0) :
    ContDiff ℝ ∞ (fun u : ℝ × ℝ =>
      hillPhysicalH1Synthesis (hillIntegerCanonicalKdVFlow 1 q u.1) u.2) := by
  let e := hillIntegerSobolevEquiv 1
  let freq := oddPositiveFrequency (fun n => hillRoughKdVFrequency n (hillIntegerSourceInclusion 1 q))
  let Z := fun u : ℝ × ℝ => fourierRealZeroSpatialTranslation
    (Weight.signedSobolev (signedStepOrder (1/2) 1)) (Weight.signedSobolev_neg _) u.2
      (fourierRealZeroPhaseFlow _ freq (oddPositiveFrequency_neg _) u.1 (e.equiv q))
  have hZ : ContDiff ℝ ∞ Z := contDiff_finite_phase_space_time _ _ freq
    (oddPositiveFrequency_neg _) (e.equiv q) S hq
  have hInv : ContDiff ℝ ∞ e.equiv.symm := contDiff_iff_contDiffAt.mpr
    (fun z => AnalyticAt.contDiffAt (F := RealSignedHilbert (signedStepOrder 0 1)) (e.analytic_symm z))
  let L : RealSignedHilbert (signedStepOrder 0 1) →L[ℝ] ℂ :=
    (((ContinuousMap.evalCLM ℂ (0 : AddCircle (2 : ℝ))).comp
      periodOneSobolevSynthesis).restrictScalars ℝ).comp signedOneRealToScalarDomain
  have hL : ContDiff ℝ ∞ (fun a : RealSignedHilbert (signedStepOrder 0 1) => L a) :=
    @ContinuousLinearMap.contDiff ℝ (RealSignedHilbert (signedStepOrder 0 1)) ℂ
      inferInstance inferInstance inferInstance inferInstance inferInstance ∞ L
  have h := hL.comp (hInv.comp hZ)
  have he (u : ℝ × ℝ) : L (e.equiv.symm (Z u)) =
      hillPhysicalH1Synthesis (hillIntegerCanonicalKdVFlow 1 q u.1) u.2 := by
    change hillPhysicalH1Synthesis (e.equiv.symm (Z u)) 0 = _
    dsimp only [Z]
    rw [e.spatial_symm]
    change hillPhysicalH1Synthesis
      (fourierRealZeroSpatialTranslation _ _ u.2 (hillIntegerCanonicalKdVFlow 1 q u.1)) 0 = _
    rw [hillPhysicalH1Synthesis_spatialTranslation, zero_add]
  simpa only [Function.comp_def, he] using! h

theorem contDiff_hillFiniteNative_H4_space_time
    (q : RealSignedHilbert (signedStepOrder 0 4)) (S : Finset ℤ)
    (hq : ∀ k ∉ S, ((hillIntegerSobolevEquiv 4).equiv q).val.val.val k = 0) :
    ContDiff ℝ ∞ (fun u : ℝ × ℝ =>
      hillPhysicalH4Synthesis (hillIntegerCanonicalKdVFlow 4 q u.1) u.2) := by
  have hfin (k : ℤ) (hk : k ∉ S) :
      ((hillIntegerSobolevEquiv 1).equiv (hillIntegerSourceOrderInclusion 1 4 (by decide) q)).val.val.val k = 0 := by
    rw [hillIntegerSobolevEquiv_order_compatibility, hillIntegerTargetOrderInclusion_apply]
    exact hq k hk
  have he : (fun u : ℝ × ℝ => hillPhysicalH4Synthesis (hillIntegerCanonicalKdVFlow 4 q u.1) u.2) =
      (fun u : ℝ × ℝ => hillPhysicalH1Synthesis
        (hillIntegerCanonicalKdVFlow 1 (hillIntegerSourceOrderInclusion 1 4 (by decide) q) u.1) u.2) := by
    funext u
    rw [hillIntegerCanonicalKdVFlow_order_compatibility]
    rfl
  rw [he]
  exact contDiff_hillFiniteNative_H1_space_time _ S hfin

end NLS.Articles.KdVPseudomeasures
