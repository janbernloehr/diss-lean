import NLS.SequenceSpaces.SignedSobolevSpatialLift

/-! Spatially covariant analytic equivalences lift to adjacent Sobolev
orders in both directions, without spectral or inverse-regularity premises. -/
noncomputable section
open Complex
namespace NLS.WeightedCoeff

structure SignedSpatialAnalyticEquiv (s t : ℝ) where
  equiv : RealSignedHilbert s ≃ RealSignedHilbert t
  analytic : ∀ a, AnalyticAt ℝ equiv a
  analytic_symm : ∀ z, AnalyticAt ℝ equiv.symm z
  spatial : ∀ a x, equiv (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg s) x a)=
    fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg t) x (equiv a)

namespace SignedSpatialAnalyticEquiv
variable {s t : ℝ} (e : SignedSpatialAnalyticEquiv s t)

theorem spatial_apply (a : RealSignedHilbert s) (x : ℝ) (k : ℤ) :
    (e.equiv (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg s) x a)).val.val.val k=
      exp (((x*(2*Real.pi*k):ℝ):ℂ)*I)*(e.equiv a).val.val.val k := by
  rw [e.spatial,fourierRealZeroSpatialTranslation_apply]

theorem spatial_symm (z : RealSignedHilbert t) (x : ℝ) :
    e.equiv.symm (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg t) x z)=
      fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg s) x (e.equiv.symm z) := by
  apply e.equiv.injective
  rw [e.equiv.apply_symm_apply,e.spatial,e.equiv.apply_symm_apply]

theorem spatial_symm_apply (z : RealSignedHilbert t) (x : ℝ) (k : ℤ) :
    (e.equiv.symm (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg t) x z)).val.val.val k=
      exp (((x*(2*Real.pi*k:ℝ):ℝ):ℂ)*I)*(e.equiv.symm z).val.val.val k := by
  rw [e.spatial_symm,fourierRealZeroSpatialTranslation_apply]

def succEquiv : RealSignedHilbert (s+1) ≃ RealSignedHilbert (t+1) where
  toFun := signedSpatialLift s t e.equiv
  invFun := signedSpatialLift t s e.equiv.symm
  left_inv a := by
    apply signedRealInclusion_injective s
    rw [signedSpatialLift_inclusion t s e.equiv.symm e.analytic_symm e.spatial_symm_apply,
      signedSpatialLift_inclusion s t e.equiv e.analytic e.spatial_apply,e.equiv.symm_apply_apply]
  right_inv z := by
    apply signedRealInclusion_injective t
    rw [signedSpatialLift_inclusion s t e.equiv e.analytic e.spatial_apply,
      signedSpatialLift_inclusion t s e.equiv.symm e.analytic_symm e.spatial_symm_apply,e.equiv.apply_symm_apply]

theorem succEquiv_inclusion (a : RealSignedHilbert (s+1)) :
    signedRealInclusion t (e.succEquiv a)=e.equiv (signedRealInclusion s a) :=
  signedSpatialLift_inclusion s t e.equiv e.analytic e.spatial_apply a

theorem succEquiv_apply (a : RealSignedHilbert (s+1)) (k : ℤ) :
    (e.succEquiv a).val.val.val k=(e.equiv (signedRealInclusion s a)).val.val.val k :=
  signedSpatialLift_apply s t e.equiv e.analytic e.spatial_apply a k

def succ : SignedSpatialAnalyticEquiv (s+1) (t+1) where
  equiv := e.succEquiv
  analytic a := analyticAt_signedSpatialLift s t e.equiv a (e.analytic _)
  analytic_symm z := analyticAt_signedSpatialLift t s e.equiv.symm z (e.analytic_symm _)
  spatial a x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    rw [e.succEquiv_apply,fourierRealZeroSpatialTranslation_apply,e.succEquiv_apply]
    have hi : signedRealInclusion s
        (fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg (s+1)) x a)=
        fourierRealZeroSpatialTranslation _ (Weight.signedSobolev_neg s) x (signedRealInclusion s a) := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext j
      rw [signedRealInclusion_apply,fourierRealZeroSpatialTranslation_apply,
        fourierRealZeroSpatialTranslation_apply,signedRealInclusion_apply]
    rw [hi,e.spatial_apply]

end SignedSpatialAnalyticEquiv
end NLS.WeightedCoeff
