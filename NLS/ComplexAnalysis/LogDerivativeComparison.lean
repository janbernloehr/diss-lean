import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Stable logarithmic derivatives away from zeros -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem norm_logDeriv_sub_le {f g : ℂ → ℂ} (z : ℂ) {b ε δ M : ℝ}
    (hb : 0 < b) (hf : b ≤ ‖f z‖) (hg : b ≤ ‖g z‖)
    (hε : ‖f z-g z‖ ≤ ε) (hδ : ‖deriv f z-deriv g z‖ ≤ δ)
    (hM : ‖deriv g z‖ ≤ M) :
    ‖logDeriv f z-logDeriv g z‖ ≤ δ/b+M*ε/b^2 := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hfn : f z ≠ 0 := norm_pos_iff.mp (hb.trans_le hf)
  have hgn : g z ≠ 0 := norm_pos_iff.mp (hb.trans_le hg)
  have he : logDeriv f z-logDeriv g z =
      (deriv f z-deriv g z)/f z-deriv g z*(f z-g z)/(f z*g z) := by
    simp only [logDeriv_apply]
    field_simp
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [norm_div,norm_div,norm_mul,norm_mul]
  apply add_le_add
  · exact div_le_div₀ hδ0 hδ hb hf
  · apply div_le_div₀ (mul_nonneg hM0 hε0) (mul_le_mul hM hε (norm_nonneg _) ((norm_nonneg _).trans hM))
      (sq_pos_of_pos hb)
    nlinarith [mul_le_mul hf hg hb.le (norm_nonneg (f z))]

end NLS.ComplexAnalysis
