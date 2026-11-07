import Mathlib.Analysis.Complex.Basic

/-! A quadratic factorization transfers a weighted coefficient error
to the raw remainder, including at a collapsed quadratic factor. -/
set_option autoImplicit false
namespace NLS.ComplexAnalysis

theorem weighted_quadratic_remainder_bound
    (w M : ℝ) (g a b c : ℂ) (ha : a=g^2/4*(b+c)) (hc : w*‖c‖≤M) :
    w*‖a-b*g^2/4‖≤‖g‖^2*M/4 := by
  have he : a-b*g^2/4=g^2/4*c := by rw [ha];ring
  rw [he,norm_mul,norm_div,norm_pow]
  norm_num only [Complex.norm_ofNat]
  calc
    _=(‖g‖^2*(w*‖c‖))/4 := by ring
    _≤‖g‖^2*M/4 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (sq_nonneg _)) (by norm_num)

end NLS.ComplexAnalysis
