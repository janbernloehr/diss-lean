import NLS.ComplexAnalysis.LaurentSquareRemainder

/-! # Weighted square errors for an inverse-frequency phase -/

noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem norm_square_error_of_phase_error_general (m : ℕ) (F P z : ℂ) (D B : ℝ)
    (hz : 1 ≤ ‖z‖) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hP : ‖P‖ ≤ B*‖z‖) (herror : ‖z‖^(m+1) * ‖F-P‖ ≤ D) :
    ‖z‖^m * ‖F^2-P^2‖ ≤ D*(2*B+D) := by
  have hr : 0 ≤ ‖z‖ := norm_nonneg _
  have hr5 : 1 ≤ ‖z‖^(m+1) := one_le_pow₀ hz
  have he : ‖F-P‖ ≤ D := by nlinarith [norm_nonneg (F-P)]
  have hF : ‖F‖ ≤ (B+D)*‖z‖ := by
    have ht := norm_add_le (F-P) P
    rw [sub_add_cancel] at ht
    nlinarith
  have hsum : ‖F‖+‖P‖ ≤ (2*B+D)*‖z‖ := by nlinarith
  have heq : F^2-P^2 = (F-P)*(F+P) := by ring
  rw [heq, norm_mul]
  have ht : ‖z‖^m * (‖F-P‖*‖F+P‖) ≤
      ‖z‖^m * (‖F-P‖*((2*B+D)*‖z‖)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans hsum) (norm_nonneg _)) (by positivity)
  calc
    _ ≤ ‖z‖^m * (‖F-P‖*((2*B+D)*‖z‖)) := ht
    _ = (2*B+D)*(‖z‖^(m+1)*‖F-P‖) := by rw [pow_succ]; ring
    _ ≤ (2*B+D)*D := mul_le_mul_of_nonneg_left herror (by positivity)
    _ = _ := by ring



theorem norm_square_model_energy_error_le (z a b : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖z‖^5 * ‖(-I*z+a/z^3+b/z^5)^2+z^2+(2*I*a)/z^2+(2*I*b)/z^4‖ ≤
      ‖a‖^2+2*‖a‖*‖b‖+‖b‖^2 := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : (-I*z+a/z^3+b/z^5)^2+z^2+(2*I*a)/z^2+(2*I*b)/z^4 =
      a^2/z^6+(2*a*b)/z^8+b^2/z^10 := by
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [he]
  have ht : ‖a^2/z^6+(2*a*b)/z^8+b^2/z^10‖ ≤
      ‖a^2/z^6‖+‖(2*a*b)/z^8‖+‖b^2/z^10‖ := by
    have h12 := norm_add_le (a^2/z^6) ((2*a*b)/z^8)
    have h123 := norm_add_le (a^2/z^6+(2*a*b)/z^8) (b^2/z^10)
    linarith
  have hh := mul_le_mul_of_nonneg_left ht (pow_nonneg (norm_nonneg z) 5)
  simp only [mul_add] at hh
  have h1 := norm_weighted_laurent_term_le z (a^2) hz 5 6 (by omega)
  have h2 := norm_weighted_laurent_term_le z (2*a*b) hz 5 8 (by omega)
  have h3 := norm_weighted_laurent_term_le z (b^2) hz 5 10 (by omega)
  simp only [norm_mul, norm_ofNat, norm_pow] at h1 h2 h3
  linarith

theorem norm_square_energy_error_of_phase_error (z F a b : ℂ) (D : ℝ)
    (hz : 1 ≤ ‖z‖) (hD : 0 ≤ D)
    (herror : ‖z‖^6 * ‖F-(-I*z+a/z^3+b/z^5)‖ ≤ D) :
    ‖z‖^5 * ‖F^2+z^2+(2*I*a)/z^2+(2*I*b)/z^4‖ ≤
      D*(2*(1+‖a‖+‖b‖)+D) + ‖a‖^2+2*‖a‖*‖b‖+‖b‖^2 := by
  let P := -I*z+a/z^3+b/z^5
  have hPa : ‖a/z^3‖ ≤ ‖a‖ := by
    simpa only [pow_zero, one_mul] using norm_weighted_laurent_term_le z a hz 0 3 (by omega)
  have hPb : ‖b/z^5‖ ≤ ‖b‖ := by
    simpa only [pow_zero, one_mul] using norm_weighted_laurent_term_le z b hz 0 5 (by omega)
  have hP : ‖P‖ ≤ (1+‖a‖+‖b‖)*‖z‖ := by
    have h1 := norm_add_le (-I*z) (a/z^3)
    have h2 := norm_add_le (-I*z+a/z^3) (b/z^5)
    simp only [norm_mul,norm_neg,norm_I,one_mul] at h1
    dsimp only [P]
    nlinarith [norm_nonneg a,norm_nonneg b]
  have hfirst := norm_square_error_of_phase_error_general 5 F P z D (1+‖a‖+‖b‖)
    hz hD (by positivity) hP herror
  have hmodel := norm_square_model_energy_error_le z a b hz
  have heq : F^2+z^2+(2*I*a)/z^2+(2*I*b)/z^4 =
      (F^2-P^2)+(P^2+z^2+(2*I*a)/z^2+(2*I*b)/z^4) := by ring
  rw [heq]
  have ht := mul_le_mul_of_nonneg_left
    (norm_add_le (F^2-P^2) (P^2+z^2+(2*I*a)/z^2+(2*I*b)/z^4))
    (pow_nonneg (norm_nonneg z) 5)
  rw [mul_add] at ht
  change ‖z‖^5*‖P^2+z^2+(2*I*a)/z^2+(2*I*b)/z^4‖ ≤ _ at hmodel
  linarith


end NLS.ComplexAnalysis
