import NLS.ComplexAnalysis.QuadraticEnergySheet

/-! A frequency representative for a translated quadratic energy.
Its sign is chosen near the original frequency at infinity; the exact
square and quantitative displacement do not require a real shift. -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

def shiftedFrequency (a z : ℂ) : ℂ := z*Complex.sqrt (1+a/z^2)

theorem norm_sqrt_one_add_sub_one_le (a : ℂ) : ‖Complex.sqrt (1+a)-1‖ ≤ ‖a‖ := by
  let r := Complex.sqrt (1+a)
  have hs : r^2 = 1+a := complex_sqrt_sq _
  have hfactor : (r-1)*(r+1) = a := by linear_combination hs
  have hplus : 1 ≤ ‖r+1‖ := by
    have hr : 0 ≤ r.re := re_sqrt_nonneg _
    have hn := Complex.re_le_norm (r+1)
    simp only [add_re,one_re] at hn
    linarith
  have hn := congrArg norm hfactor
  rw [norm_mul] at hn
  change ‖r-1‖ ≤ ‖a‖
  nlinarith [norm_nonneg (r-1)]

theorem shiftedFrequency_sq (a z : ℂ) (hz : z ≠ 0) : (shiftedFrequency a z)^2 = z^2+a := by
  rw [shiftedFrequency,mul_pow,complex_sqrt_sq]
  field_simp

theorem norm_shiftedFrequency_sub_le (a z : ℂ) (hz : z ≠ 0) :
    ‖shiftedFrequency a z-z‖ ≤ ‖a‖/‖z‖ := by
  have he : shiftedFrequency a z-z = z*(Complex.sqrt (1+a/z^2)-1) := by
    dsimp only [shiftedFrequency]
    ring
  rw [he,norm_mul]
  calc
    _ ≤ ‖z‖*‖a/z^2‖ := mul_le_mul_of_nonneg_left (norm_sqrt_one_add_sub_one_le _) (norm_nonneg _)
    _ = ‖a‖/‖z‖ := by
      rw [norm_div,norm_pow]
      field_simp

theorem exists_threshold_shiftedFrequency_close (a : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖shiftedFrequency a z-z‖ ≤ δ := by
  refine ⟨1+‖a‖/δ,by positivity,?_⟩
  intro z hz
  have hdiv : 0 ≤ ‖a‖/δ := div_nonneg (norm_nonneg _) hδ.le
  have hn : 0 < ‖z‖ := by linarith
  have hb : ‖a‖ ≤ δ*‖z‖ := by
    have h := mul_le_mul_of_nonneg_left (show ‖a‖/δ ≤ ‖z‖ by linarith) hδ.le
    simpa only [mul_div_cancel₀ _ hδ.ne'] using h
  exact (norm_shiftedFrequency_sub_le a z (norm_pos_iff.mp hn)).trans ((div_le_iff₀ hn).mpr (by linarith))

theorem shiftedFrequency_norm_bounds (a z : ℂ) (hz : 2 ≤ ‖z‖)
    (hd : ‖shiftedFrequency a z-z‖ ≤ 1) :
    0 < ‖shiftedFrequency a z‖ ∧ ‖z‖/2 ≤ ‖shiftedFrequency a z‖ ∧
      ‖z‖/‖shiftedFrequency a z‖ ≤ 2 := by
  have ht := norm_sub_norm_le z (shiftedFrequency a z)
  rw [norm_sub_rev] at ht
  have hlow : ‖z‖/2 ≤ ‖shiftedFrequency a z‖ := by linarith
  have hpos : 0 < ‖shiftedFrequency a z‖ := by linarith
  exact ⟨hpos,hlow,(div_le_iff₀ hpos).mpr (by linarith)⟩

end NLS.ComplexAnalysis
