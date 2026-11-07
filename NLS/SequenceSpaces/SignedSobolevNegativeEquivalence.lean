import NLS.SequenceSpaces.SignedSobolevPositiveEquivalence
import NLS.SequenceSpaces.FourierRealEquivalentWeights
import NLS.SequenceSpaces.SignedOrderHalfFourierEquiv

/-! Coefficient-preserving comparison at negative orders, with the
correct reversed weight inequalities and explicit constants. -/
noncomputable section
namespace NLS.Weight

theorem sobolev_negative_le_signed (r : ℝ) (hr : 0 ≤ r) (k : ℤ) :
    sobolev (-r) k ≤ signedSobolev (-r) k := by
  apply Real.rpow_le_rpow_of_nonpos (by positivity)
    (max_le (by linarith [abs_nonneg (k:ℝ)]) (by linarith)) (by linarith)

theorem signed_negative_le_two_rpow_sobolev (r : ℝ) (hr : 0 ≤ r) (k : ℤ) :
    signedSobolev (-r) k ≤ (2:ℝ)^r*sobolev (-r) k := by
  have hb : 1+|(k:ℝ)| ≤ 2*max 1 |(k:ℝ)| := by
    linarith [le_max_left (1:ℝ) |(k:ℝ)|, le_max_right (1:ℝ) |(k:ℝ)|]
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < 1+|(k:ℝ)|) hb
    (show -r ≤ 0 by linarith)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)] at hpow
  calc
    _ = (2:ℝ)^r*((2:ℝ)^(-r)*(max 1 |(k:ℝ)|)^(-r)) := by
      rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2), add_neg_cancel, Real.rpow_zero, one_mul]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

end NLS.Weight
namespace NLS.WeightedCoeff
open scoped ENNReal

def signedSobolevNegativeEquiv (r : ℝ) (hr : 0 ≤ r) :
    WeightedCoeff (Weight.signedSobolev (-r)) 2 ≃L[ℂ] WeightedCoeff (Weight.sobolev (-r)) 2 :=
  WeightComparison.equiv _ _ 1 ((2:ℝ)^r) zero_le_one (by positivity)
    (fun k => by simpa only [one_mul] using Weight.sobolev_negative_le_signed r hr k)
    (Weight.signed_negative_le_two_rpow_sobolev r hr)

theorem signedSobolevNegativeEquiv_apply (r : ℝ) (hr : 0 ≤ r)
    (a : WeightedCoeff (Weight.signedSobolev (-r)) 2) (k : ℤ) :
    (signedSobolevNegativeEquiv r hr a).val k = a.val k :=
  WeightComparison.equiv_apply _ _ _ _ _ _ _ _ a k

theorem signedSobolevNegativeEquiv_symm_apply (r : ℝ) (hr : 0 ≤ r)
    (a : WeightedCoeff (Weight.sobolev (-r)) 2) (k : ℤ) :
    ((signedSobolevNegativeEquiv r hr).symm a).val k = a.val k :=
  WeightComparison.equiv_symm_apply _ _ _ _ _ _ _ _ a k

def physicalSignedSobolevNegativeEquiv (r : ℝ) (hr : 0 ≤ r) :
    fourierRealZeroSubmodule (Weight.signedSobolev (-r)) 2 ≃L[ℝ]
      fourierRealZeroSubmodule (Weight.sobolev (-r)) 2 :=
  fourierRealWeightEquiv _ _ (Weight.signedSobolev_neg _) (Weight.sobolev_neg _)
    1 ((2:ℝ)^r) zero_le_one (by positivity)
    (fun k => by simpa only [one_mul] using Weight.sobolev_negative_le_signed r hr k)
    (Weight.signed_negative_le_two_rpow_sobolev r hr)

theorem physicalSignedSobolevNegativeEquiv_apply (r : ℝ) (hr : 0 ≤ r)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (-r)) 2) (k : ℤ) :
    (physicalSignedSobolevNegativeEquiv r hr a).val.val.val k = a.val.val.val k :=
  fourierRealWeightEquiv_apply _ _ _ _ _ _ _ _ _ _ a k

theorem physicalSignedSobolevNegativeEquiv_symm_apply (r : ℝ) (hr : 0 ≤ r)
    (a : fourierRealZeroSubmodule (Weight.sobolev (-r)) 2) (k : ℤ) :
    ((physicalSignedSobolevNegativeEquiv r hr).symm a).val.val.val k = a.val.val.val k :=
  fourierRealWeightEquiv_symm_apply _ _ _ _ _ _ _ _ _ _ a k

def signedOrderHalfFourierEquivOfEq (s t : ℝ) (ht : t = s+1/2) :
    WeightedCoeff (Weight.signedSobolev s) 2 ≃L[ℂ] WeightedCoeff (Weight.signedSobolev t) 2 := by
  subst t
  exact signedOrderHalfFourierEquiv s 2

theorem signedOrderHalfFourierEquivOfEq_apply (s t : ℝ) (ht : t = s+1/2)
    (a : WeightedCoeff (Weight.signedSobolev s) 2) (k : ℤ) :
    (signedOrderHalfFourierEquivOfEq s t ht a).val k = halfFourierSymbol k*a.val k := by
  subst t
  exact signedOrderHalfFourierEquiv_apply s 2 a k

def negativeSobolevHalfFourierEquiv (r : ℝ) (hr : 0 ≤ r) :
    WeightedCoeff (Weight.sobolev (-r)) 2 ≃L[ℂ] WeightedCoeff (Weight.signedSobolev (1/2-r)) 2 :=
  (signedSobolevNegativeEquiv r hr).symm.trans
    (signedOrderHalfFourierEquivOfEq (-r) (1/2-r) (by ring))

theorem negativeSobolevHalfFourierEquiv_apply (r : ℝ) (hr : 0 ≤ r)
    (a : WeightedCoeff (Weight.sobolev (-r)) 2) (k : ℤ) :
    (negativeSobolevHalfFourierEquiv r hr a).val k = halfFourierSymbol k*a.val k := by
  rw [negativeSobolevHalfFourierEquiv, ContinuousLinearEquiv.trans_apply,
    signedOrderHalfFourierEquivOfEq_apply, signedSobolevNegativeEquiv_symm_apply]

end NLS.WeightedCoeff
