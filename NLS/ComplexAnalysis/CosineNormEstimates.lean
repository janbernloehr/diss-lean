import NLS.ComplexAnalysis.SineNormEstimates

/-! # Complex cosine Taylor and frequency comparison estimates -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_complex_cos_sub_one_le_sq (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖cos z-1‖ ≤ ‖z‖^2 := by
  have hp := Complex.norm_exp_sub_one_sub_id_le (x := z*I) (by simpa using hz)
  have hm := Complex.norm_exp_sub_one_sub_id_le (x := -(z*I)) (by simpa using hz)
  have he : cos z-1 = ((exp (z*I)-1-z*I)+(exp (-(z*I))-1-(-(z*I))))/2 := by
    rw [cos,neg_mul]
    ring
  rw [he,norm_div,norm_ofNat]
  have h := norm_add_le (exp (z*I)-1-z*I) (exp (-(z*I))-1-(-(z*I)))
  simp only [norm_neg,norm_mul,norm_I,mul_one] at hp hm
  linarith

theorem norm_complex_cos_sub_le_exp (z w : ℂ) :
    ‖cos z-cos w‖ ≤ Real.exp (|w.im|+‖z-w‖)*‖z-w‖ := by
  have hb (u : ℂ) (hu : u ∈ closedBall w ‖z-w‖) :
      ‖-sin u‖ ≤ Real.exp (|w.im|+‖z-w‖) := by
    rw [norm_neg]
    apply (norm_complex_sin_le_exp_im u).trans
    apply Real.exp_le_exp.mpr
    have hh := abs_add_le (u-w).im w.im
    rw [sub_im,sub_add_cancel] at hh
    have hi : |u.im-w.im| ≤ ‖z-w‖ := by
      simpa only [sub_im] using (abs_im_le_norm (u-w)).trans (mem_closedBall_iff_norm.mp hu)
    linarith
  exact (convex_closedBall w ‖z-w‖ : Convex ℝ (closedBall w ‖z-w‖)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hasDerivAt_cos u).hasDerivWithinAt) hb
    (mem_closedBall_self (norm_nonneg _)) (mem_closedBall_iff_norm.mpr le_rfl)

end NLS.ComplexAnalysis
