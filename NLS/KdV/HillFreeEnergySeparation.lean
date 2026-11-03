import NLS.KdV.HillFreeGapContourGeometry

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem freeHillValue_nat_separation (m k : ℕ) (hmk : m ≠ k) :
    ((m : ℝ)+(k : ℝ))*Real.pi^2 ≤
      ‖(freeHillValue m : ℂ)-(freeHillValue k : ℂ)‖ := by
  have hd : freeHillValue m-freeHillValue k =
      ((m : ℝ)^2-(k : ℝ)^2)*Real.pi^2 := by
    simp only [freeHillValue,Int.cast_natCast]
    ring
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,hd,
    abs_mul,abs_of_nonneg (sq_nonneg Real.pi)]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg Real.pi)
  rcases lt_or_gt_of_ne hmk with h | h
  · have hcast : (m : ℝ)+1 ≤ k := by exact_mod_cast h
    rw [abs_of_nonpos (by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m), (Nat.cast_nonneg k : (0:ℝ) ≤ k)])]
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ)-(m : ℝ)-1 by linarith)
      (show 0 ≤ (k : ℝ)+(m : ℝ) by positivity)]
  · have hcast : (k : ℝ)+1 ≤ m := by exact_mod_cast h
    rw [abs_of_nonneg (by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m), (Nat.cast_nonneg k : (0:ℝ) ≤ k)])]
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ)-(k : ℝ)-1 by linarith)
      (show 0 ≤ (m : ℝ)+(k : ℝ) by positivity)]

end NLS.KdV
