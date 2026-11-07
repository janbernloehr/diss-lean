import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt

/-! The exact positive Fourier square-root normalization. -/
noncomputable section
namespace NLS.RealAnalysis

theorem complex_sqrt_two_pi_mul_nat (n : ℕ) :
    (Real.sqrt (2*Real.pi*n):ℂ)=
      ((Real.sqrt Real.pi*Real.sqrt n:ℝ):ℂ)*(Real.sqrt 2:ℂ) := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi),Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  simp only [Complex.ofReal_mul]
  ring

theorem complex_sqrt_two_pi_mul_pnat_ne_zero (n : ℕ+) :
    (Real.sqrt (2*Real.pi*(n:ℕ)):ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact ne_of_gt (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) (by exact_mod_cast n.pos)))

end NLS.RealAnalysis
