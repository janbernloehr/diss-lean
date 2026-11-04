import NLS.ComplexAnalysis.NormalizedSquareRootBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal

namespace NLS.ComplexAnalysis



theorem norm_inv_sqrt_sub_one_le (w : ℂ) (hw : ‖w-1‖ ≤ 1/2) :
    ‖(Complex.sqrt w)⁻¹-1‖ ≤ 2*‖w-1‖ := by
  have hs := norm_sqrt_sub_one_le w
  have hden : 1/2 ≤ ‖Complex.sqrt w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (Complex.sqrt w)
    rw [norm_one,norm_sub_rev] at h
    linarith
  have hne : Complex.sqrt w ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : (Complex.sqrt w)⁻¹-1 = -(Complex.sqrt w-1)/Complex.sqrt w := by
    field_simp
    ring
  rw [he,norm_div,norm_neg]
  apply (div_le_iff₀ (norm_pos_iff.mpr hne)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden (show 0 ≤ 2*‖w-1‖ by positivity)]

theorem mem_slitPlane_of_norm_sub_one_le_half (w : ℂ) (hw : ‖w-1‖ ≤ 1/2) :
    w ∈ slitPlane := by
  have h := (abs_re_le_norm (w-1)).trans hw
  simp only [sub_re,one_re] at h
  apply mem_slitPlane_iff.mpr
  exact Or.inl (by linarith [(abs_le.mp h).1])

end NLS.ComplexAnalysis
