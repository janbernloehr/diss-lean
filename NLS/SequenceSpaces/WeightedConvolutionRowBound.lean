import NLS.SequenceSpaces.SpectralWeight

/-! A normalized weighted convolution entry is dominated by the
weighted kernel magnitude and the uniform reciprocal-symbol bound. -/
noncomputable section
namespace NLS

theorem norm_weighted_convolution_term_le (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 < B)
    (hC : 0 ≤ C) (hweight : A ≤ C*B) (q r f : ℂ) (δ : ℝ)
    (hr : ‖r‖ ≤ δ) :
    ‖(A:ℂ)*q*r*f/(B:ℂ)‖ ≤ δ*(C*‖q‖)*‖f‖ := by
  rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hA, Real.norm_of_nonneg hB.le]
  have hratio : A/B ≤ C := (div_le_iff₀ hB).mpr hweight
  calc
    _ = (A/B)*‖q‖*‖r‖*‖f‖ := by ring
    _ ≤ C*‖q‖*δ*‖f‖ := by gcongr
    _ = _ := by ring

end NLS
