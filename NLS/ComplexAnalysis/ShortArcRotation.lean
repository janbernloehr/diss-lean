import NLS.ComplexAnalysis.EqualNormRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Short rotations between equal complex radii stay no farther from
the starting point than their endpoint. The collapsed circle is included. -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

/-- Chord distance is monotone with absolute angle on the principal arc. -/
theorem norm_exp_I_sub_one_le_of_abs_le (x y : ℝ) (hxy : |x| ≤ |y|) (hy : |y| ≤ Real.pi) :
    ‖exp (I*x)-1‖ ≤ ‖exp (I*y)-1‖ := by
  have hx : |x| ≤ Real.pi := hxy.trans hy
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi/2) ≤ |x|/2 by linarith [abs_nonneg x,Real.pi_pos])
    (show |y|/2 ≤ Real.pi/2 by linarith) (show |x|/2 ≤ |y|/2 by linarith)
  rw [Complex.norm_exp_I_mul_ofReal_sub_one,Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith [Real.pi_pos]),
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith [Real.pi_pos]),
    abs_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact mul_le_mul_of_nonneg_left hs (by norm_num)

/-- Every point of the principal rotation arc has controlled chord distance. -/
theorem norm_short_rotation_sub_le (a : ℂ) (θ u : ℝ) (hθ : |θ| ≤ Real.pi)
    (hu : u ∈ Icc (0:ℝ) 1) :
    ‖exp (I*((u*θ:ℝ):ℂ))*a-a‖ ≤ ‖exp (I*θ)*a-a‖ := by
  have h := norm_exp_I_sub_one_le_of_abs_le (u*θ) θ
    (by rw [abs_mul,abs_of_nonneg hu.1]; exact mul_le_of_le_one_left (abs_nonneg θ) hu.2) hθ
  have he (t : ℝ) : exp (I*t)*a-a=(exp (I*t)-1)*a := by ring
  rw [he,he,norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg a)

/-- Equal radii admit a principal rotation, with the SAME endpoint and
uniform chord control along its ENTIRE path, including radius zero. -/
theorem exists_short_rotation_of_norm_eq (a b : ℂ) (hab : ‖a‖=‖b‖) :
    ∃ θ : ℝ, |θ| ≤ Real.pi ∧ exp (I*θ)*a=b ∧
      ∀ u ∈ Icc (0:ℝ) 1, ‖exp (I*((u*θ:ℝ):ℂ))*a-a‖ ≤ ‖b-a‖ := by
  by_cases ha : a=0
  · have hb : b=0 := norm_eq_zero.mp (by rw [← hab,ha,norm_zero])
    refine ⟨0,by simpa only [abs_zero] using Real.pi_pos.le,by simp [ha,hb],?_⟩
    intro u _
    simp [ha,hb]
  · let z := b/a
    have hn : ‖z‖=1 := by rw [norm_div,← hab,div_self (norm_ne_zero_iff.mpr ha)]
    have he : exp (I*z.arg)*a=b := by
      have hp := norm_mul_exp_arg_mul_I z
      rw [hn,Complex.ofReal_one,one_mul,mul_comm (z.arg:ℂ) I] at hp
      rw [hp]
      exact div_mul_cancel₀ b ha
    refine ⟨z.arg,Complex.abs_arg_le_pi z,he,?_⟩
    intro u hu
    simpa only [he] using norm_short_rotation_sub_le a z.arg u (Complex.abs_arg_le_pi z) hu

end NLS.ComplexAnalysis
