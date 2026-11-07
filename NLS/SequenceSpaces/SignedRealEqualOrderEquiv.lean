import NLS.SequenceSpaces.SignedSobolevSpatialLift

/-! A literal equality of real orders induces the coefficient identity
between the corresponding physical signed Hilbert models. -/
noncomputable section
namespace NLS.WeightedCoeff

def signedRealEqualOrderEquiv (s t : ℝ) (hst : s=t) : RealSignedHilbert s ≃L[ℝ] RealSignedHilbert t := by
  subst t
  exact ContinuousLinearEquiv.refl ℝ _

theorem signedRealEqualOrderEquiv_apply (s t : ℝ) (hst : s=t)
    (a : RealSignedHilbert s) (k : ℤ) :
    (signedRealEqualOrderEquiv s t hst a).val.val.val k = a.val.val.val k := by
  subst t
  rfl

end NLS.WeightedCoeff
