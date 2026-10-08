import NLS.ComplexAnalysis.SignedProductEstimates
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The signed linear term in Remark D.3

D.1 defines A as the norm of the sum. D.3 must instead subtract the complex
sum itself. A single negative coefficient refutes the literal reuse of A.
-/
noncomputable section
namespace NLS.ComplexAnalysis

/-- An admissible singleton whose signed sum is negative. -/
def productEstimateNegativeSingleton (n : ℤ) : ℂ := if n = 0 then -1/4 else 0

/-- The counterexample satisfies all summability and half-unit hypotheses. -/
theorem productEstimateNegativeSingleton_admissible :
    Summable (fun n => ‖productEstimateNegativeSingleton n‖) ∧
      ∀ n, ‖productEstimateNegativeSingleton n‖ ≤ (1:ℝ)/2 := by
  constructor
  · simpa only [productEstimateNegativeSingleton, apply_ite norm, norm_zero] using
      (hasSum_ite_eq (0:ℤ) (‖(-1/4:ℂ)‖)).summable
  · intro n
    by_cases h : n = 0 <;> norm_num [productEstimateNegativeSingleton, h, norm_div]

/-- Literal reuse of D.1's nonnegative A in D.3 gives a false estimate. -/
theorem printed_D3_absolute_linear_term_fails :
    ¬ (‖(∏' n : ℤ, (1+productEstimateNegativeSingleton n))-1-
          (‖∑' n : ℤ, productEstimateNegativeSingleton n‖:ℂ)‖ ≤
      ‖∑' n : ℤ, productEstimateNegativeSingleton n‖^2/2*
          Real.exp (∑' n : ℤ, ‖productEstimateNegativeSingleton n‖)+
        (∑' n : ℤ, ‖productEstimateNegativeSingleton n‖^2)*
          Real.exp ((∑' n : ℤ, ‖productEstimateNegativeSingleton n‖)+
            (∑' n : ℤ, ‖productEstimateNegativeSingleton n‖)^2)) := by
  have hp : (∏' n : ℤ, (1+productEstimateNegativeSingleton n)) = (3/4:ℂ) := by
    have he : (fun n : ℤ => 1+productEstimateNegativeSingleton n) =
        (fun n : ℤ => if n = 0 then (3/4:ℂ) else 1) := by
      funext n
      by_cases h : n = 0 <;> norm_num [productEstimateNegativeSingleton, h]
    rw [he]
    simp
  have ha : (∑' n : ℤ, productEstimateNegativeSingleton n) = (-1/4:ℂ) := by
    simp [productEstimateNegativeSingleton]
  have hs : (∑' n : ℤ, ‖productEstimateNegativeSingleton n‖) = (1:ℝ)/4 := by
    norm_num [productEstimateNegativeSingleton, apply_ite, norm_div]
  have hb : (∑' n : ℤ, ‖productEstimateNegativeSingleton n‖^2) = (1:ℝ)/16 := by
    norm_num [productEstimateNegativeSingleton, apply_ite, norm_div]
  rw [hp, ha, hs, hb]
  norm_num [norm_div]
  have he1 : Real.exp ((1:ℝ)/4) ≤ 3 :=
    (Real.exp_le_exp.mpr (by norm_num : (1:ℝ)/4 ≤ 1)).trans Real.exp_one_lt_three.le
  have he2 : Real.exp ((5:ℝ)/16) ≤ 3 :=
    (Real.exp_le_exp.mpr (by norm_num : (5:ℝ)/16 ≤ 1)).trans Real.exp_one_lt_three.le
  nlinarith

end NLS.ComplexAnalysis
