import Mathlib.Analysis.Complex.Basic

/-! Scalar control of the actual squared-gap off-diagonal remainder. -/
namespace NLS

theorem cubic_offset_remainder_small_bound
    (G A C δ : ℝ) (hA : 0≤A) (hC : 0≤C) (hδ : 0≤δ)
    (hGδ : G≤δ) (hAC : A≤C) (hδ1 : δ≤1) :
    G*A/4+2*(G*A+1/2)*(δ*(δ+1)+δ/4) ≤ δ*(8*C+8) := by
  have hGA : G*A≤δ*C := mul_le_mul hGδ hAC hA hδ
  have hGA1 : G*A≤C := hGA.trans (by nlinarith)
  have he : δ*(δ+1)+δ/4≤(9/4)*δ := by nlinarith
  calc
    _ ≤ δ*C/4+2*(C+1/2)*((9/4)*δ) := by gcongr
    _ ≤ δ*(8*C+8) := by nlinarith [mul_nonneg hδ hC]

end NLS
