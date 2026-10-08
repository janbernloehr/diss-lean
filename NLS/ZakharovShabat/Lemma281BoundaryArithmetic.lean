import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Auditing the final scalar comparison in Lemma 28.1

These are arithmetic statements, not spectral counterexamples. The printed
comparison fails at n=N; a strictly exterior index recovers the printed constant.
-/
namespace NLS.ZakharovShabat

/-- The displayed ratio does not satisfy the claimed bound at the first boundary index. -/
theorem lemma281_ratio_boundary_counterexample :
    ¬ (((1:ℝ)+1+2/5)/(1-1+3/10) ≤ 2*(1+1)) := by norm_num

/-- Even with the cutoff chosen as in the proof, the displayed chain to 2048 fails at n=N. -/
theorem lemma281_constant_boundary_counterexample :
    (10:ℝ) < 8*(21/16) ∧ 8*(21/16:ℝ) ≤ 10+1 ∧
      ¬ (128*((10:ℝ)+10+2/5)/(10-10+3/10) ≤ 2048*(1+21/16)) := by norm_num

/-- An inclusive boundary index admits the safe factor-eight scalar estimate. -/
theorem lemma281_ratio_le_eight (N n : ℝ) (hN : 0 ≤ N) (hn : N ≤ n) :
    (n+N+2/5)/(n-N+3/10) ≤ 8*(N+1) := by
  apply (div_le_iff₀ (by linarith : 0 < n-N+3/10)).mpr
  nlinarith [mul_nonneg hN (sub_nonneg.mpr hn)]

/-- One index beyond the cutoff, the printed factor-two comparison is valid. -/
theorem lemma281_ratio_le_two_of_exterior (N n : ℝ) (hN : 0 ≤ N) (hn : N+1 ≤ n) :
    (n+N+2/5)/(n-N+3/10) ≤ 2*(N+1) := by
  apply (div_le_iff₀ (by linarith : 0 < n-N+3/10)).mpr
  nlinarith [mul_nonneg hN (by linarith : 0 ≤ n-N-1)]

/-- The scalar chain retains 2048 at strictly exterior indices with the chosen cutoff. -/
theorem lemma281_scalar_constant_of_exterior (N n Q : ℝ) (hN : 0 ≤ N)
    (hn : N+1 ≤ n) (hcut : N ≤ 8*Q) :
    128*((n+N+2/5)/(n-N+3/10)) ≤ 2048*(1+Q) := by
  have h := mul_le_mul_of_nonneg_left (lemma281_ratio_le_two_of_exterior N n hN hn)
    (by norm_num : (0:ℝ) ≤ 128)
  linarith

/-- Keeping the boundary index instead gives an inclusive scalar chain with constant 8192. -/
theorem lemma281_scalar_constant_inclusive (N n Q : ℝ) (hN : 0 ≤ N)
    (hn : N ≤ n) (hcut : N ≤ 8*Q) :
    128*((n+N+2/5)/(n-N+3/10)) ≤ 8192*(1+Q) := by
  have h := mul_le_mul_of_nonneg_left (lemma281_ratio_le_eight N n hN hn)
    (by norm_num : (0:ℝ) ≤ 128)
  linarith

end NLS.ZakharovShabat
