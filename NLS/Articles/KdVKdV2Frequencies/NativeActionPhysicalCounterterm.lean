import NLS.Articles.KdVKdV2Frequencies.NativeActionNormalization
import NLS.Articles.KdVKdV2Frequencies.OriginalRoughActionGerms

/-! The literal normalized native counterterm is the actual signed
Birkhoff product, at every eligible source order and physical label. -/
noncomputable section
open Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem nativeActionCoordinates_raw_product
    (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (a : physicalRealDeletedSubmodule) (n : ℕ+) :
    nativeActionCoordinates D t ht a (actionIndexEquiv.symm n)/(Weight.sobolev (2*t-1) (n:ℤ):ℂ)=
      D.roughActionCoordinate n (GlobalRoughAbelianForwardData.realNativeSource t ht a) := by
  have he : positiveIndexInjection actionIndexEquiv (actionIndexEquiv.symm n)=(n:ℤ) :=
    congrArg (fun m : ℕ+ => (m:ℤ)) (actionIndexEquiv.apply_symm_apply n)
  have hL (j : ℤ) : (D.realNativeForward t ht a).val.val j/(Weight.sobolev (t-1/2) j:ℂ)=
      (D.signed (GlobalRoughAbelianForwardData.realNativeSource t ht a)).val j :=
    congrArg (fun q : WeightedCoeff (Weight.sobolev (t-1/2)) 2 => q.val j)
      (D.realNativeForward_target_lift t ht a)
  have hw : (Weight.sobolev (2*t-1) (n:ℤ):ℂ)=
      (Weight.sobolev (t-1/2) (n:ℤ):ℂ)*(Weight.sobolev (t-1/2) (n:ℤ):ℂ) := by
    rw [show 2*t-1=(t-1/2)+(t-1/2) by ring,Weight.sobolev_add,Complex.ofReal_mul]
  rw [nativeActionCoordinates,quadraticActions_deletedToSignedPair_apply,he,hw,mul_div_mul_comm,hL]
  rw [←Weight.sobolev_neg (t-1/2) (n:ℤ),hL]
  rfl

end NLS.Articles.KdVKdV2Frequencies
