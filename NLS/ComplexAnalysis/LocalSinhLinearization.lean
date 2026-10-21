import NLS.ComplexAnalysis.LocalSinhComparison
import Mathlib.Analysis.Complex.Exponential

/-! # Local quadratic control of hyperbolic sine

The quadratic Taylor estimate and local inverse comparison control the error when recovering a small phase from its sine.
-/

noncomputable section
open Complex
namespace NLS.ComplexAnalysis

/-- The exponential Taylor bounds give a quadratic remainder for the
hyperbolic sine on the closed unit disc. -/
theorem norm_sinh_sub_self_le_sq (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖sinh z-z‖ ≤ ‖z‖^2 := by
  have h₁ := Complex.norm_exp_sub_one_sub_id_le hz
  have h₂ := Complex.norm_exp_sub_one_sub_id_le (x := -z) (by simpa using hz)
  have he : sinh z-z = ((exp z-1-z)-(exp (-z)-1-(-z)))/2 := by
    rw [sinh]
    ring
  rw [he,norm_div,norm_ofNat]
  have h := norm_sub_le (exp z-1-z) (exp (-z)-1-(-z))
  simp only [norm_neg] at h₂
  linarith

/-- Near zero, the inverse hyperbolic-sine remainder has a quadratic
bound in the phase and its sine value, with one common radius. -/
theorem exists_norm_sinh_inverse_remainder_bound :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, ‖z‖ < ε →
      ‖z‖ ≤ 2*‖sinh z‖ ∧ ‖z-sinh z‖ ≤ 2*‖z‖*‖sinh z‖ := by
  obtain ⟨ε,hε,h⟩ := exists_norm_sub_le_two_mul_sinh_sub
  refine ⟨min ε 1,lt_min hε zero_lt_one,?_⟩
  intro z hz
  have hsmall : ‖z‖ ≤ 2*‖sinh z‖ := by
    simpa only [sub_zero,sinh_zero] using h z 0 (hz.trans_le (min_le_left _ _))
      (by simpa only [norm_zero] using hε)
  refine ⟨hsmall,?_⟩
  rw [norm_sub_rev]
  exact (norm_sinh_sub_self_le_sq z (hz.le.trans (min_le_right _ _))).trans (by
    nlinarith [norm_nonneg z])

end NLS.ComplexAnalysis
