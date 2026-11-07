import NLS.SequenceSpaces.HalfFourierEquiv

/-! The same exact Fourier symbol between the literal source and target
orders -r and one-half minus r, at every Banach exponent including infinity. -/
noncomputable section
open scoped ENNReal
namespace NLS.Weight

theorem signedSobolev_half_sub (r : ℝ) (k : ℤ) :
    signedSobolev (1/2-r) k=Real.sqrt (max 1 |(k:ℝ)|)*signedSobolev (-r) k := by
  have hb : (0:ℝ) < max 1 |(k:ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  change (max 1 |(k:ℝ)|)^(1/2-r)=_
  rw [sub_eq_add_neg,Real.rpow_add hb,← Real.sqrt_eq_rpow]
  rfl

theorem signedSobolev_negative_bounds (r : ℝ) (hr : 0 ≤ r) (k : ℤ) :
    sobolev (-r) k ≤ signedSobolev (-r) k ∧
      signedSobolev (-r) k ≤ (2:ℝ)^r*sobolev (-r) k := by
  have hb : (0:ℝ) < max 1 |(k:ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hba : max 1 |(k:ℝ)| ≤ 1+|(k:ℝ)| :=
    max_le (by linarith [abs_nonneg (k:ℝ)]) (by linarith)
  have hab : 1+|(k:ℝ)| ≤ 2*max 1 |(k:ℝ)| := by
    nlinarith [le_max_left (1:ℝ) |(k:ℝ)|,le_max_right (1:ℝ) |(k:ℝ)|]
  constructor
  · exact Real.rpow_le_rpow_of_nonpos hb hba (neg_nonpos.mpr hr)
  · have h := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < 1+|(k:ℝ)|)
      hab (neg_nonpos.mpr hr)
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hb.le] at h
    have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) r)
    rw [← mul_assoc,← Real.rpow_add (by norm_num : (0:ℝ) < 2),add_neg_cancel,Real.rpow_zero,one_mul] at hm
    exact hm

end NLS.Weight
namespace NLS.WeightedCoeff

theorem halfFourierSymbol_negative_order_bound (r : ℝ) (hr : 0 ≤ r) (k : ℤ) :
    Weight.signedSobolev (1/2-r) k*‖halfFourierSymbol k‖ ≤
      ((2:ℝ)^r/Real.sqrt (2*Real.pi))*Weight.sobolev (-r) k := by
  have hb : (0:ℝ) < max 1 |(k:ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [Weight.signedSobolev_half_sub,halfFourierSymbol,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (mul_pos hc (Real.sqrt_pos.mpr hb)))]
  calc
    _ = Weight.signedSobolev (-r) k/Real.sqrt (2*Real.pi) := by
      field_simp [hc.ne',ne_of_gt (Real.sqrt_pos.mpr hb)]
    _ ≤ ((2:ℝ)^r*Weight.sobolev (-r) k)/Real.sqrt (2*Real.pi) :=
      div_le_div_of_nonneg_right (Weight.signedSobolev_negative_bounds r hr k).2 hc.le
    _ = _ := by ring

theorem halfFourierInverseSymbol_negative_order_bound (r : ℝ) (hr : 0 ≤ r) (k : ℤ) :
    Weight.sobolev (-r) k*‖halfFourierInverseSymbol k‖ ≤
      Real.sqrt (2*Real.pi)*Weight.signedSobolev (1/2-r) k := by
  have hb : (0:ℝ) < max 1 |(k:ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [Weight.signedSobolev_half_sub,halfFourierInverseSymbol,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (mul_pos hc (Real.sqrt_pos.mpr hb))]
  calc
    _ ≤ Weight.signedSobolev (-r) k*(Real.sqrt (2*Real.pi)*Real.sqrt (max 1 |(k:ℝ)|)) :=
      mul_le_mul_of_nonneg_right (Weight.signedSobolev_negative_bounds r hr k).1 (by positivity)
    _ = _ := by ring

def negativeOrderHalfFourierEquiv (r : ℝ) (hr : 0 ≤ r) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeff (Weight.sobolev (-r)) p ≃L[ℂ] WeightedCoeff (Weight.signedSobolev (1/2-r)) p :=
  weightedMultiplierEquiv _ _ halfFourierSymbol halfFourierInverseSymbol
    ((2:ℝ)^r/Real.sqrt (2*Real.pi)) (Real.sqrt (2*Real.pi)) (by positivity) (by positivity)
    (halfFourierSymbol_negative_order_bound r hr) (halfFourierInverseSymbol_negative_order_bound r hr)
    halfFourierSymbol_mul_inverse

theorem negativeOrderHalfFourierEquiv_apply (r : ℝ) (hr : 0 ≤ r) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WeightedCoeff (Weight.sobolev (-r)) p) (k : ℤ) :
    (negativeOrderHalfFourierEquiv r hr p a).val k=halfFourierSymbol k*a.val k := rfl

theorem negativeOrderHalfFourierEquiv_symm_apply (r : ℝ) (hr : 0 ≤ r) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WeightedCoeff (Weight.signedSobolev (1/2-r)) p) (k : ℤ) :
    ((negativeOrderHalfFourierEquiv r hr p).symm a).val k=halfFourierInverseSymbol k*a.val k := rfl

end NLS.WeightedCoeff
