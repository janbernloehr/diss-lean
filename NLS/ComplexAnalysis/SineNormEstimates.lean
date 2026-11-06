import NLS.ComplexAnalysis.DuhamelIntegralBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # Complex sine Taylor, inverse and frequency comparison estimates -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_complex_sin_sub_self_le_sq (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖sin z-z‖ ≤ ‖z‖^2 := by
  have hp := Complex.norm_exp_sub_one_sub_id_le (x := z*I) (by simpa using hz)
  have hm := Complex.norm_exp_sub_one_sub_id_le (x := -(z*I)) (by simpa using hz)
  have he : (sin z-z)*I = ((exp (z*I)-1-z*I)-(exp (-(z*I))-1-(-(z*I))))/2 := by
    rw [sin]
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  have h := norm_sub_le (exp (z*I)-1-z*I) (exp (-(z*I))-1-(-(z*I)))
  rw [← mul_one ‖sin z-z‖,← norm_I,← norm_mul,he,norm_div,norm_ofNat]
  simp only [norm_neg,norm_mul,norm_I,mul_one] at hp hm
  linarith

theorem norm_le_two_mul_complex_sin (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    ‖z‖ ≤ 2*‖sin z‖ := by
  have h := norm_complex_sin_sub_self_le_sq z (hz.trans (by norm_num))
  have ht := norm_le_norm_sub_add z (sin z)
  rw [norm_sub_rev] at ht
  nlinarith [norm_nonneg z]

theorem norm_complex_sin_sub_le_exp (z w : ℂ) :
    ‖sin z-sin w‖ ≤ Real.exp (|w.im|+‖z-w‖)*‖z-w‖ := by
  have hb (u : ℂ) (hu : u ∈ closedBall w ‖z-w‖) :
      ‖cos u‖ ≤ Real.exp (|w.im|+‖z-w‖) := by
    apply (norm_complex_cos_le_exp_im u).trans
    apply Real.exp_le_exp.mpr
    have hh := abs_add_le (u-w).im w.im
    rw [sub_im,sub_add_cancel] at hh
    have hi : |u.im-w.im| ≤ ‖z-w‖ := by
      simpa only [sub_im] using (abs_im_le_norm (u-w)).trans (mem_closedBall_iff_norm.mp hu)
    linarith
  exact (convex_closedBall w ‖z-w‖ : Convex ℝ (closedBall w ‖z-w‖)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hasDerivAt_sin u).hasDerivWithinAt) hb
    (mem_closedBall_self (norm_nonneg _)) (mem_closedBall_iff_norm.mpr le_rfl)

end NLS.ComplexAnalysis
