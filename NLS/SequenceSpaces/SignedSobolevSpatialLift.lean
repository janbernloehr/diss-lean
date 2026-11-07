import NLS.SequenceSpaces.SignedSobolevRealScale
import NLS.FunctionalAnalysis.AnalyticGeneratorRecovery

/-! An analytic spatially covariant map lifts analytically by one full
Sobolev order. The lifted map has exactly the original entire output. -/
noncomputable section
open Complex Filter Topology
namespace NLS.WeightedCoeff

abbrev RealSignedHilbert (s : ℝ) := fourierRealZeroSubmodule (Weight.signedSobolev s) 2

def signedSpatialLift (s t : ℝ) (f : RealSignedHilbert s → RealSignedHilbert t)
    (a : RealSignedHilbert (s+1)) : RealSignedHilbert (t+1) :=
  signedRealSpatialRecovery t ((fderiv ℝ f (signedRealInclusion s a))
    (fourierRealZeroSignedSpatialGenerator s a))

theorem analyticAt_signedSpatialLift (s t : ℝ)
    (f : RealSignedHilbert s → RealSignedHilbert t) (a : RealSignedHilbert (s+1))
    (hf : AnalyticAt ℝ f (signedRealInclusion s a)) :
    AnalyticAt ℝ (signedSpatialLift s t f) a := by
  exact @NLS.FunctionalAnalysis.analyticAt_derivative_generator_recovery ℝ
    (RealSignedHilbert s) (RealSignedHilbert t) (RealSignedHilbert (s+1)) (RealSignedHilbert (t+1))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance f
    (signedRealInclusion s) (fourierRealZeroSignedSpatialGenerator s)
    (signedRealSpatialRecovery t) a hf

theorem signedSpatialLift_inclusion (s t : ℝ)
    (f : RealSignedHilbert s → RealSignedHilbert t)
    (hf : ∀ a, AnalyticAt ℝ f a)
    (hc : ∀ (a : RealSignedHilbert s) (x : ℝ) (k : ℤ),
      (f (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg s) x a)).val.val.val k=
        exp (((x*(2*Real.pi*k):ℝ):ℂ)*I)*(f a).val.val.val k)
    (a : RealSignedHilbert (s+1)) :
    signedRealInclusion t (signedSpatialLift s t f a)=f (signedRealInclusion s a) := by
  let q := signedRealInclusion s a
  let v := fourierRealZeroSignedSpatialGenerator s a
  let γ : ℝ → RealSignedHilbert s := fun x =>
    fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg s) x q
  have hv (k : ℤ) : v.val.val.val k=I*((2*Real.pi*k:ℝ):ℂ)*q.val.val.val k := by
    rw [fourierRealZeroSignedSpatialGenerator_apply,signedRealInclusion_apply]
  have hd : HasDerivAt γ v 0 := hasDerivAt_fourierRealZero_spatialCurve _
    (Weight.signedSobolev_neg s) (by norm_num) q v hv γ
      (fun x k => fourierRealZeroSpatialTranslation_apply _ _ x q k)
  have hγ0 : γ 0=q := fourierRealZeroSpatialTranslation_zero _ _ q
  have hcomp := @NLS.FunctionalAnalysis.hasDerivAt_differentiable_comp
    (RealSignedHilbert s) (RealSignedHilbert t)
    inferInstance inferInstance inferInstance inferInstance f γ v 0
    (by rw [hγ0]; exact (hf q).differentiableAt) hd
  rw [hγ0] at hcomp
  have hD := fourierRealZero_spatialGenerator_of_hasDerivAt (Weight.signedSobolev t)
    (f q) ((fderiv ℝ f q) v) (fun x => f (γ x)) (fun x k => hc q x k) hcomp
  exact signedRealInclusion_recovery t _ _ hD

theorem signedSpatialLift_apply (s t : ℝ)
    (f : RealSignedHilbert s → RealSignedHilbert t)
    (hf : ∀ a, AnalyticAt ℝ f a)
    (hc : ∀ (a : RealSignedHilbert s) (x : ℝ) (k : ℤ),
      (f (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg s) x a)).val.val.val k=
        exp (((x*(2*Real.pi*k):ℝ):ℂ)*I)*(f a).val.val.val k)
    (a : RealSignedHilbert (s+1)) (k : ℤ) :
    (signedSpatialLift s t f a).val.val.val k=(f (signedRealInclusion s a)).val.val.val k := by
  have he := congrArg (fun z => z.val.val.val k) (signedSpatialLift_inclusion s t f hf hc a)
  simpa only [signedRealInclusion_apply] using he

end NLS.WeightedCoeff
