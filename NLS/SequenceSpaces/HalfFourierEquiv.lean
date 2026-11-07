import NLS.SequenceSpaces.SignedSobolevWeight
import NLS.SequenceSpaces.WeightedMultiplierEquiv
import NLS.RealAnalysis.HalfFourierWeightBounds

/-! The exact half-derivative weighted Fourier multiplier and its bounded
inverse, for every Banach exponent, including infinity. -/
noncomputable section
open scoped ENNReal
namespace NLS.Weight

theorem signedSobolev_neg_half (k : ℤ) :
    signedSobolev (-1/2) k=1/Real.sqrt (max 1 |(k:ℝ)|) := by
  have hb : (0:ℝ) < max 1 |(k:ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  change (max 1 |(k:ℝ)|)^(-1/2:ℝ)=_
  rw [show (-1/2:ℝ) = -(1/2) by ring,Real.rpow_neg hb.le,← Real.sqrt_eq_rpow,one_div]

end NLS.Weight
namespace NLS.WeightedCoeff

def halfFourierSymbol (k : ℤ) : ℂ :=
  ((1/(Real.sqrt (2*Real.pi)*Real.sqrt (max 1 |(k:ℝ)|)):ℝ):ℂ)

def halfFourierInverseSymbol (k : ℤ) : ℂ :=
  ((Real.sqrt (2*Real.pi)*Real.sqrt (max 1 |(k:ℝ)|):ℝ):ℂ)

theorem halfFourierSymbol_neg (k : ℤ) : halfFourierSymbol (-k)=halfFourierSymbol k := by
  simp only [halfFourierSymbol,Int.cast_neg,abs_neg]

theorem halfFourierSymbol_positive (n : ℕ+) :
    halfFourierSymbol ((n:ℕ):ℤ)=1/(Real.sqrt (2*Real.pi*(n:ℕ)):ℂ) := by
  have hn : (1:ℝ) ≤ (n:ℕ) := by exact_mod_cast (Nat.succ_le_of_lt n.pos)
  change ((1/(Real.sqrt (2*Real.pi)*Real.sqrt (max 1 |((n:ℕ):ℝ)|)):ℝ):ℂ)=_
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℕ)),max_eq_right hn]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi)]
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul]

theorem halfFourierSymbol_mul_inverse (k : ℤ) : halfFourierSymbol k*halfFourierInverseSymbol k=1 := by
  unfold halfFourierSymbol halfFourierInverseSymbol
  rw [← Complex.ofReal_mul]
  have hb : (0:ℝ) < max 1 |(k:ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [one_div_mul_cancel (ne_of_gt (mul_pos hc (Real.sqrt_pos.mpr hb))),Complex.ofReal_one]

theorem halfFourierSymbol_bound (k : ℤ) :
    Weight.signedSobolev (-1/2) k*‖halfFourierSymbol k‖ ≤
      (2/Real.sqrt (2*Real.pi))*Weight.sobolev (-1) k := by
  have hb : (0:ℝ) < max 1 |(k:ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hab : 1+|(k:ℝ)| ≤ 2*max 1 |(k:ℝ)| := by nlinarith [le_max_left (1:ℝ) |(k:ℝ)|,le_max_right (1:ℝ) |(k:ℝ)|]
  rw [halfFourierSymbol,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr (mul_pos hc (Real.sqrt_pos.mpr hb))),
    Weight.signedSobolev_neg_half,Weight.sobolev_apply,Real.rpow_neg_one,← one_div]
  exact NLS.RealAnalysis.halfFourier_forward_bound _ _ _ (by positivity) hb hc hab

theorem halfFourierInverseSymbol_bound (k : ℤ) :
    Weight.sobolev (-1) k*‖halfFourierInverseSymbol k‖ ≤
      Real.sqrt (2*Real.pi)*Weight.signedSobolev (-1/2) k := by
  have hb : (0:ℝ) < max 1 |(k:ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hba : max 1 |(k:ℝ)| ≤ 1+|(k:ℝ)| := max_le (by linarith [abs_nonneg (k:ℝ)]) (by linarith)
  rw [halfFourierInverseSymbol,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (mul_pos hc (Real.sqrt_pos.mpr hb)),
    Weight.signedSobolev_neg_half,Weight.sobolev_apply,Real.rpow_neg_one,← one_div]
  exact NLS.RealAnalysis.halfFourier_inverse_bound _ _ _ (by positivity) hb hc hba

def halfFourierEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeff (Weight.sobolev (-1)) p ≃L[ℂ] WeightedCoeff (Weight.signedSobolev (-1/2)) p :=
  weightedMultiplierEquiv _ _ halfFourierSymbol halfFourierInverseSymbol
    (2/Real.sqrt (2*Real.pi)) (Real.sqrt (2*Real.pi)) (by positivity) (by positivity)
    halfFourierSymbol_bound halfFourierInverseSymbol_bound halfFourierSymbol_mul_inverse

theorem halfFourierEquiv_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WeightedCoeff (Weight.sobolev (-1)) p) (k : ℤ) :
    (halfFourierEquiv p a).val k=halfFourierSymbol k*a.val k := rfl

theorem halfFourierEquiv_symm_apply (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WeightedCoeff (Weight.signedSobolev (-1/2)) p) (k : ℤ) :
    ((halfFourierEquiv p).symm a).val k=halfFourierInverseSymbol k*a.val k := rfl

end NLS.WeightedCoeff
