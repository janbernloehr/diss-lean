import NLS.Articles.KdVKdV2Frequencies.GlobalWeakInverseSource
import NLS.Articles.KdVKdV2Frequencies.NativeSourceFiniteActionVariation

/-! Exact weak normalization of the ORIGINAL native positive actions.
The weak normalized action is the raw original action multiplied by the
Sobolev weight of order minus one. No signed or Cartesian factor is lost. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

def nativeWeakSignedTarget (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) : physicalRealDeletedSubmodule :=
  ⟨WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2)) (D.signed (nativeHillSource m q.val)),
    meanZeroWeightedProjection_real _ (Weight.sobolev_neg (-1/2)) _
      (D.signed_real _ (nativeHillSource_real m q.val q.property.1))⟩

/-- The SAME global weak inverse recovers the entire original native source. -/
theorem nativeWeakSignedTarget_inverse (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    D.realWeakInverseSource (D.nativeWeakSignedTarget m q)=nativeHillSource m q.val :=
  D.realWeakInverseSource_of_signed _ (nativeHillSource_real m q.val q.property.1)
    (by simpa only [nativeHillSource_apply] using q.property.2)

/-- Actual weak normalized positive actions, in their original weak l1 norm. -/
def nativeWeakActionSequence (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) : Coeff 1 :=
  quadraticActionsExponent (q := 1) (Coeff.signedToCartesian (D.nativeWeakSignedTarget m q).val)

/-- EVERY coefficient is exactly the original native action times its
weak Sobolev weight, zero extended to nonpositive indices. -/
theorem nativeWeakActionSequence_apply (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (j : ℤ) :
    D.nativeWeakActionSequence m q j = (Weight.sobolev (-1) j : ℂ)*(D.nativeSourceActionSequence m r hrs q).val j := by
  rw [nativeWeakActionSequence,Coeff.quadraticActions_signedToCartesian,D.nativeSourceActionSequence_apply]
  by_cases hj : 0<j
  · rw [if_pos hj,if_pos hj]
    have hj0 : j≠0 := by omega
    have hnj0 : -j≠0 := by omega
    change (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
      (D.signed (nativeHillSource m q.val))).val j*
      (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
        (D.signed (nativeHillSource m q.val))).val (-j)=_
    rw [WeightedCoeff.meanZeroWeightedProjection_apply_other _ _ j hj0,
      WeightedCoeff.meanZeroWeightedProjection_apply_other _ _ (-j) hnj0,Weight.sobolev_neg]
    have hw : (Weight.sobolev (-1/2) j)^2=Weight.sobolev (-1) j := by
      rw [pow_two,←Weight.sobolev_add]
      norm_num
    have hwc : (Weight.sobolev (-1/2) j : ℂ)^2=(Weight.sobolev (-1) j : ℂ) := by exact_mod_cast hw
    rw [←hwc]
    ring
  · rw [if_neg hj,if_neg hj,mul_zero]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
