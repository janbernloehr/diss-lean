import NLS.SequenceSpaces.RealMeanZeroHalfFourierEquiv
import NLS.SequenceSpaces.FourierRealZeroMultiplier

/-! The original half-Fourier symbol at EVERY real signed source order
and EVERY Banach exponent, including the literal Wiener endpoint p=1.
The physical real zero-mode equivalence retains the exact 2*pi scalar. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Weight

theorem signedSobolev_add_half (s : ℝ) (k : ℤ) :
    signedSobolev (s + 1/2) k = Real.sqrt (max 1 |(k : ℝ)|) * signedSobolev s k := by
  have hb : 0 < max 1 |(k : ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  change (max 1 |(k : ℝ)|)^(s + 1/2) = _
  rw [Real.rpow_add hb, ← Real.sqrt_eq_rpow, mul_comm]
  rfl

end NLS.Weight
namespace NLS.WeightedCoeff

theorem halfFourierSymbol_signed_order_bound (s : ℝ) (k : ℤ) :
    Weight.signedSobolev (s + 1/2) k * ‖halfFourierSymbol k‖ ≤
      (1 / Real.sqrt (2 * Real.pi)) * Weight.signedSobolev s k := by
  have hb : 0 < Real.sqrt (max 1 |(k : ℝ)|) := Real.sqrt_pos.mpr
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hc : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [Weight.signedSobolev_add_half, halfFourierSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (mul_pos hc hb))]
  apply le_of_eq
  field_simp

theorem halfFourierInverseSymbol_signed_order_bound (s : ℝ) (k : ℤ) :
    Weight.signedSobolev s k * ‖halfFourierInverseSymbol k‖ ≤
      Real.sqrt (2 * Real.pi) * Weight.signedSobolev (s + 1/2) k := by
  have hb : 0 < Real.sqrt (max 1 |(k : ℝ)|) := Real.sqrt_pos.mpr
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hc : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [Weight.signedSobolev_add_half, halfFourierInverseSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos hc hb)]
  exact le_of_eq (by ring)

def signedOrderHalfFourierEquiv (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeff (Weight.signedSobolev s) p ≃L[ℂ]
      WeightedCoeff (Weight.signedSobolev (s + 1/2)) p :=
  weightedMultiplierEquiv _ _ halfFourierSymbol halfFourierInverseSymbol
    (1 / Real.sqrt (2 * Real.pi)) (Real.sqrt (2 * Real.pi)) (by positivity) (by positivity)
    (halfFourierSymbol_signed_order_bound s) (halfFourierInverseSymbol_signed_order_bound s)
    halfFourierSymbol_mul_inverse

theorem signedOrderHalfFourierEquiv_apply (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WeightedCoeff (Weight.signedSobolev s) p) (k : ℤ) :
    (signedOrderHalfFourierEquiv s p a).val k = halfFourierSymbol k * a.val k := rfl

theorem signedOrderHalfFourierEquiv_symm_apply (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WeightedCoeff (Weight.signedSobolev (s + 1/2)) p) (k : ℤ) :
    ((signedOrderHalfFourierEquiv s p).symm a).val k = halfFourierInverseSymbol k * a.val k := rfl

def signedRealOrderHalfFourierEquiv (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    fourierRealZeroSubmodule (Weight.signedSobolev s) p ≃L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev (s + 1/2)) p := by
  let A := fourierRealZeroMultiplier (p := p) (Weight.signedSobolev s) (Weight.signedSobolev (s + 1/2))
    (Weight.signedSobolev_neg _) halfFourierSymbol (1 / Real.sqrt (2 * Real.pi))
    (by positivity) (halfFourierSymbol_signed_order_bound s)
    (fun k => (halfFourierSymbol_neg k).trans (halfFourierSymbol_conj k).symm)
  let B := fourierRealZeroMultiplier (p := p) (Weight.signedSobolev (s + 1/2)) (Weight.signedSobolev s)
    (Weight.signedSobolev_neg _) halfFourierInverseSymbol (Real.sqrt (2 * Real.pi))
    (by positivity) (halfFourierInverseSymbol_signed_order_bound s)
    (fun k => (halfFourierInverseSymbol_neg k).trans (halfFourierInverseSymbol_conj k).symm)
  refine { toLinearEquiv := { A.toLinearMap with invFun := B, left_inv := ?_, right_inv := ?_ }
           continuous_toFun := A.continuous, continuous_invFun := B.continuous }
  · intro a
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    change (B (A a)).val.val.val k = a.val.val.val k
    rw [fourierRealZeroMultiplier_apply, fourierRealZeroMultiplier_apply]
    rw [← mul_assoc, mul_comm (halfFourierInverseSymbol k), halfFourierSymbol_mul_inverse, one_mul]
  · intro a
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    change (A (B a)).val.val.val k = a.val.val.val k
    rw [fourierRealZeroMultiplier_apply, fourierRealZeroMultiplier_apply,
      ← mul_assoc, halfFourierSymbol_mul_inverse, one_mul]

theorem signedRealOrderHalfFourierEquiv_apply (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : fourierRealZeroSubmodule (Weight.signedSobolev s) p) (k : ℤ) :
    (signedRealOrderHalfFourierEquiv s p a).val.val.val k = halfFourierSymbol k * a.val.val.val k :=
  fourierRealZeroMultiplier_apply _ _ _ _ _ _ _
    (fun j => (halfFourierSymbol_neg j).trans (halfFourierSymbol_conj j).symm) a k

theorem signedRealOrderHalfFourierEquiv_symm_apply (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (s + 1/2)) p) (k : ℤ) :
    ((signedRealOrderHalfFourierEquiv s p).symm a).val.val.val k =
      halfFourierInverseSymbol k * a.val.val.val k :=
  fourierRealZeroMultiplier_apply _ _ _ _ _ _ _
    (fun j => (halfFourierInverseSymbol_neg j).trans (halfFourierInverseSymbol_conj j).symm) a k

def signedRealOrderHalfFourierEquivOfEq (s t : ℝ) (ht : t = s + 1/2)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    fourierRealZeroSubmodule (Weight.signedSobolev s) p ≃L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev t) p := by
  subst t
  exact signedRealOrderHalfFourierEquiv s p

theorem signedRealOrderHalfFourierEquivOfEq_apply (s t : ℝ) (ht : t = s + 1/2)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : fourierRealZeroSubmodule (Weight.signedSobolev s) p) (k : ℤ) :
    (signedRealOrderHalfFourierEquivOfEq s t ht p a).val.val.val k = halfFourierSymbol k * a.val.val.val k := by
  subst t
  exact signedRealOrderHalfFourierEquiv_apply s p a k

theorem signedRealOrderHalfFourierEquivOfEq_symm_apply (s t : ℝ) (ht : t = s + 1/2)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : fourierRealZeroSubmodule (Weight.signedSobolev t) p) (k : ℤ) :
    ((signedRealOrderHalfFourierEquivOfEq s t ht p).symm a).val.val.val k =
      halfFourierInverseSymbol k * a.val.val.val k := by
  subst t
  exact signedRealOrderHalfFourierEquiv_symm_apply s p a k

end NLS.WeightedCoeff
