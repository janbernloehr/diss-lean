import NLS.SequenceSpaces.WeightedReciprocalDecay
import NLS.ComplexAnalysis.SharpExponentialRemainder

/-! # Smoothing of a complex exponential error

An inverse-bracket symbol yields an exact exponential-error multiplier gaining one derivative at every real order and Banach sequence exponent.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- An inverse-bracket complex symbol gives an exact exponential-error multiplier gaining one derivative. -/
theorem exists_sobolev_complex_phase_gain_multiplier {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (r t : ℝ) (f : ℤ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ n : ℤ, (1+|(n:ℝ)|)*‖f n‖ ≤ K) :
    ∃ T : WeightedCoeff (Weight.sobolev r) q →L[ℂ] WeightedCoeff (Weight.sobolev (r+1)) q,
      (∀ c n, (T c).val n = (exp ((t:ℂ)*Complex.I*f n)-1)*c.val n) ∧
      ‖T‖ ≤ |t| *K*Real.exp (|t| *K) := by
  apply exists_sobolev_gain_multiplier r _ (|t| *K*Real.exp (|t| *K)) (by positivity)
  intro n
  have hfn : ‖f n‖ ≤ K := (by nlinarith [abs_nonneg (n:ℝ),norm_nonneg (f n)] :
    ‖f n‖ ≤ (1+|(n:ℝ)|)*‖f n‖).trans (hf n)
  have hnorm : ‖(t:ℂ)*Complex.I*f n‖ = |t| *‖f n‖ := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  have he : ‖exp ((t:ℂ)*Complex.I*f n)-1‖ ≤ |t| *‖f n‖*Real.exp (|t| *K) := by
    have hb := NLS.ComplexAnalysis.norm_exp_sub_one_le_norm_mul_exp ((t:ℂ)*Complex.I*f n)
    rw [hnorm] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hfn (abs_nonneg t))) (by positivity))
  calc
    _ ≤ (1+|(n:ℝ)|)*(|t| *‖f n‖*Real.exp (|t| *K)) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((1+|(n:ℝ)|)*‖f n‖)*(|t| *Real.exp (|t| *K)) := by ring
    _ ≤ K*(|t| *Real.exp (|t| *K)) := mul_le_mul_of_nonneg_right (hf n) (by positivity)
    _ = _ := by ring

end NLS.WeightedCoeff
