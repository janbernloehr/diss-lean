import NLS.ComplexAnalysis.NormalizedSquareRootBounds

/-! # A quantitative principal-square-root displacement bound from a positive real center. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
theorem norm_complexSqrt_sub_positive_le (w : ℂ) (c D : ℝ) (hc : 0 < c)
    (h : ‖w-(c : ℂ)^2‖ ≤ D) : ‖Complex.sqrt w-(c : ℂ)‖ ≤ D/c := by
  have hre : 0 ≤ (Complex.sqrt w).re := by rw [Complex.sqrt,cpow_inv_two_re]; positivity
  have hlo : c ≤ ‖Complex.sqrt w+(c : ℂ)‖ := by
    have h1 := re_le_norm (Complex.sqrt w+(c : ℂ))
    simp only [add_re,ofReal_re] at h1
    linarith
  have hs : (Complex.sqrt w)^2 = w := by
    have h1 := Complex.cpow_nat_inv_pow w (Nat.succ_ne_zero 1)
    norm_num at h1
    simpa only [Complex.sqrt,one_div] using h1
  have he : (Complex.sqrt w-(c : ℂ))*(Complex.sqrt w+(c : ℂ)) = w-(c : ℂ)^2 := by linear_combination hs
  apply (le_div_iff₀ hc).mpr
  calc
    _ ≤ ‖Complex.sqrt w-(c : ℂ)‖*‖Complex.sqrt w+(c : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hlo (norm_nonneg _)
    _ = ‖w-(c : ℂ)^2‖ := by rw [← norm_mul,he]
    _ ≤ D := h

end NLS.ComplexAnalysis
