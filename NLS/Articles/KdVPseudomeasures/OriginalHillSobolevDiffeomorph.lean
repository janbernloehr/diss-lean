import NLS.SequenceSpaces.SignedSobolevAnalyticLadder
import NLS.Articles.KdVPseudomeasures.OriginalHillL2GlobalInverse

/-! The SAME actual native Hill coordinates are a global real analytic
equivalence on EVERY nonnegative integer Hilbert Sobolev scale. This
supplies the strong domains needed for the physical KdV Hamiltonian.
It does not assert the Wiener ell-one statement of Theorem 5.1. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hillL2NativeMap_spatial_covariance (u : HillRealL2BanachSource) (x : ℝ) :
    hillL2NativeMap (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg 0) x u)=
      fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg (1/2)) x (hillL2NativeMap u) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillL2NativeMap_apply,fourierRealZeroSpatialTranslation_apply,hillL2NativeMap_apply]
  have hi : hillL2SourceInclusion
      (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg 0) x u)=
      hillRealSpatialTranslation x (hillL2SourceInclusion u) := by
    apply hillRealMeanZeroInclusion_injective
    apply Subtype.ext
    funext j
    change (hillL2SourceInclusion
      (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg 0) x u)).val.val.val j=_
    rw [hillL2SourceInclusion_apply,fourierRealZeroSpatialTranslation_apply,
      hillRealSpatialTranslation_inclusion,spatialTranslation_apply]
    rw [show (hillRealMeanZeroInclusion (hillL2SourceInclusion u)).val j=u.val.val.val j from
      hillL2SourceInclusion_apply u j]
  rw [hi,hillRealSignedMap_spatialTranslation_apply]

def hillL2SpatialAnalyticEquiv : SignedSpatialAnalyticEquiv 0 (1/2) where
  equiv := hillL2NativeHomeomorph.toEquiv
  analytic := analyticAt_hillL2NativeMap
  analytic_symm := analyticAt_hillL2NativeHomeomorph_symm
  spatial := hillL2NativeMap_spatial_covariance

/-- The source exponent is exactly N; the target is exactly N+1/2. -/
def hillIntegerSobolevEquiv (N : ℕ) :
    SignedSpatialAnalyticEquiv (signedStepOrder 0 N) (signedStepOrder (1/2) N) :=
  hillL2SpatialAnalyticEquiv.iterate N

theorem hillIntegerSobolev_source_order (N : ℕ) : signedStepOrder 0 N=(N:ℝ) := by
  rw [signedStepOrder_eq,zero_add]

theorem hillIntegerSobolev_target_order (N : ℕ) : signedStepOrder (1/2) N=(N:ℝ)+1/2 := by
  rw [signedStepOrder_eq,add_comm]

/-- Every signed native coordinate is unchanged, including the zero and
collapsed modes. The lower source has the IDENTICAL entire coefficients. -/
theorem hillIntegerSobolevEquiv_apply (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 N)) (k : ℤ) :
    ((hillIntegerSobolevEquiv N).equiv q).val.val.val k=
      (hillRealSignedMap (hillL2SourceInclusion (signedIteratedInclusion 0 N q))).val.val.val k := by
  rw [show hillIntegerSobolevEquiv N=hillL2SpatialAnalyticEquiv.iterate N from rfl,
    SignedSpatialAnalyticEquiv.iterate_inclusion_apply]
  exact hillL2NativeMap_apply _ k

theorem analyticAt_hillIntegerSobolevEquiv (N : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 N)) :
    AnalyticAt ℝ (hillIntegerSobolevEquiv N).equiv q := (hillIntegerSobolevEquiv N).analytic q

theorem analyticAt_hillIntegerSobolevEquiv_symm (N : ℕ)
    (z : RealSignedHilbert (signedStepOrder (1/2) N)) :
    AnalyticAt ℝ (hillIntegerSobolevEquiv N).equiv.symm z := (hillIntegerSobolevEquiv N).analytic_symm z

end NLS.Articles.KdVPseudomeasures
