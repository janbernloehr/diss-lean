import NLS.SequenceSpaces.SandwichMajorant

/-! # Absolute summation of conjugate-exponent convolution sandwiches

The positive sandwich realizes an absolutely convergent double series,
including the endpoint with bounded symbols and summable inputs.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Absolute summability over both indices, including the p=1 endpoint. -/
theorem summable_sandwich_terms (a : Coeff q) (φ : Coeff p)
    (b : Coeff q) (f : Coeff p) :
    Summable (fun jk : ℤ × ℤ => ‖a jk.1‖ * (‖φ (jk.1-jk.2)‖ * (‖b jk.2‖ * ‖f jk.2‖))) := by
  apply (summable_prod_of_nonneg (by intro jk; positivity)).mpr
  constructor
  · intro j
    have hb : Summable (fun k : ℤ => ‖b k‖ * ‖f k‖) := by
      simpa only [holderMultiplier_apply, norm_mul, mul_comm] using
        (lp.memℓp (holderMultiplier b f)).norm.summable_of_one
    apply (hb.mul_left (‖a j‖ * ‖φ‖)).of_nonneg_of_le (by intro k; positivity)
    intro k
    calc
      _ ≤ ‖a j‖ * (‖φ‖ * (‖b k‖ * ‖f k‖)) := by
        gcongr
        exact lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' φ (j-k)
      _ = _ := by ring
  · let u := convolutionSandwich (magnitude a) (magnitude φ) (magnitude b) (magnitude f)
    have hu := (lp.memℓp u).norm.summable_of_one
    apply hu.congr
    intro j
    change ‖u j‖ = ∑' k : ℤ, ‖a j‖ * (‖φ (j-k)‖ * (‖b k‖ * ‖f k‖))
    rw [norm_magnitude_sandwich_apply, tsum_mul_left]

/-- The absolute double sum is the norm of the positive convolution sandwich. -/
theorem tsum_sandwich_terms (a : Coeff q) (φ : Coeff p)
    (b : Coeff q) (f : Coeff p) :
    (∑' jk : ℤ × ℤ, ‖a jk.1‖ * (‖φ (jk.1-jk.2)‖ * (‖b jk.2‖ * ‖f jk.2‖))) =
      ‖convolutionSandwich (magnitude a) (magnitude φ) (magnitude b) (magnitude f)‖ := by
  rw [(summable_sandwich_terms a φ b f).tsum_prod]
  have h := (lp.hasSum_norm (p := 1) (by simp)
    (convolutionSandwich (magnitude a) (magnitude φ) (magnitude b) (magnitude f))).tsum_eq
  simpa only [Real.rpow_one, ENNReal.toReal_one, one_div, norm_magnitude_sandwich_apply,
    tsum_mul_left] using h

end NLS.Coeff
