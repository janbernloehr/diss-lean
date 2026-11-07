import NLS.SequenceSpaces.SignedSobolevAnalyticLadder

/-! Arbitrary analytic spatially covariant maps lift through all integer
Sobolev orders. Bijectivity is not assumed. Every lifted map retains the
entire original output coefficient sequence. -/
noncomputable section
open Complex
namespace NLS.WeightedCoeff

theorem signedRealInclusion_spatialTranslation (s x : ℝ) (a : RealSignedHilbert (s + 1)) :
    signedRealInclusion s (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x a) =
      fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x (signedRealInclusion s a) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [signedRealInclusion_apply, fourierRealZeroSpatialTranslation_apply,
    fourierRealZeroSpatialTranslation_apply, signedRealInclusion_apply]

theorem signedSpatialLift_spatial (s t : ℝ) (f : RealSignedHilbert s → RealSignedHilbert t)
    (hf : ∀ a, AnalyticAt ℝ f a)
    (hc : ∀ a x, f (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x a) =
      fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x (f a))
    (a : RealSignedHilbert (s + 1)) (x : ℝ) :
    signedSpatialLift s t f (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x a) =
      fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x (signedSpatialLift s t f a) := by
  have hcoord (q : RealSignedHilbert s) (y : ℝ) (k : ℤ) :
      (f (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) y q)).val.val.val k =
        exp (((y * (2 * Real.pi * k) : ℝ) : ℂ) * I) * (f q).val.val.val k := by
    rw [hc, fourierRealZeroSpatialTranslation_apply]
  apply signedRealInclusion_injective t
  rw [signedSpatialLift_inclusion s t f hf hcoord, signedRealInclusion_spatialTranslation,
    signedRealInclusion_spatialTranslation, hc, signedSpatialLift_inclusion s t f hf hcoord]

def signedAnalyticMapIterate (s t : ℝ) (f : RealSignedHilbert s → RealSignedHilbert t) :
    (N : ℕ) → RealSignedHilbert (signedStepOrder s N) → RealSignedHilbert (signedStepOrder t N)
  | 0 => f
  | N + 1 => signedSpatialLift _ _ (signedAnalyticMapIterate s t f N)

theorem analyticAt_signedAnalyticMapIterate (s t : ℝ) (f : RealSignedHilbert s → RealSignedHilbert t)
    (hf : ∀ a, AnalyticAt ℝ f a) (N : ℕ) (a : RealSignedHilbert (signedStepOrder s N)) :
    AnalyticAt ℝ (signedAnalyticMapIterate s t f N) a := by
  induction N with
  | zero => exact hf a
  | succ N ih =>
    exact analyticAt_signedSpatialLift _ _ (signedAnalyticMapIterate s t f N) a (ih _)

theorem signedAnalyticMapIterate_spatial (s t : ℝ) (f : RealSignedHilbert s → RealSignedHilbert t)
    (hf : ∀ a, AnalyticAt ℝ f a)
    (hc : ∀ a x, f (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x a) =
      fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x (f a))
    (N : ℕ) (a : RealSignedHilbert (signedStepOrder s N)) (x : ℝ) :
    signedAnalyticMapIterate s t f N (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x a) =
      fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x (signedAnalyticMapIterate s t f N a) := by
  induction N generalizing x with
  | zero => exact hc a x
  | succ N ih =>
    exact signedSpatialLift_spatial _ _ _ (analyticAt_signedAnalyticMapIterate s t f hf N) ih a x

theorem signedAnalyticMapIterate_apply (s t : ℝ) (f : RealSignedHilbert s → RealSignedHilbert t)
    (hf : ∀ a, AnalyticAt ℝ f a)
    (hc : ∀ a x, f (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x a) =
      fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x (f a))
    (N : ℕ) (a : RealSignedHilbert (signedStepOrder s N)) (k : ℤ) :
    (signedAnalyticMapIterate s t f N a).val.val.val k =
      (f (signedIteratedInclusion s N a)).val.val.val k := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hcoord (q : RealSignedHilbert (signedStepOrder s N)) (x : ℝ) (j : ℤ) :
        (signedAnalyticMapIterate s t f N
          (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg _) x q)).val.val.val j =
          exp (((x * (2 * Real.pi * j) : ℝ) : ℂ) * I) * (signedAnalyticMapIterate s t f N q).val.val.val j := by
      rw [signedAnalyticMapIterate_spatial s t f hf hc, fourierRealZeroSpatialTranslation_apply]
    change RealSignedHilbert (signedStepOrder s N + 1) at a
    change (signedSpatialLift _ _ (signedAnalyticMapIterate s t f N) a).val.val.val k =
      (f (signedIteratedInclusion s N (signedRealInclusion _ a))).val.val.val k
    exact (signedSpatialLift_apply _ _ _ (analyticAt_signedAnalyticMapIterate s t f hf N)
      hcoord a k).trans (ih _)

end NLS.WeightedCoeff
