import NLS.ZakharovShabat.SourceHilbertUniformSpectralDisplacement
import NLS.ZakharovShabat.SourceRealHigherAction

/-! # Uniform ordinary-action comparison on real Hilbert balls

The actual uniform positive endpoint lower bound and the original
higher-action mean-value formula control every high ordinary action by
the first spectrally weighted action divided by its actual index.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- One norm-dependent cutoff controls EVERY high ordinary action by the
original first weighted action, including all collapsed gaps. -/
theorem exists_uniform_real_hilbert_ordinary_action_comparison (R : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ φ : realTypeSourceSubmodule 2, ‖φ.val‖≤R →
      ∀ n : ℕ, N≤n →
        (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re ≤
          2*sourceRealHigherAction (by simp) (by norm_num) φ n 1/(Real.pi*(n : ℝ)) := by
  obtain ⟨N,hN,hbound⟩ := exists_uniform_real_hilbert_positive_endpoint_lower_bound R
  refine ⟨N,hN,?_⟩
  intro φ hφ n hn
  obtain ⟨ζ,hζ,he⟩ := sourceRealHigherAction_eq_power_mul_action
    (by simp : (2 : ℝ≥0∞)≠⊤) (by norm_num : 1<(2 : ℝ≥0∞)) φ n 1
  have hζlo := (hbound φ hφ n hn).trans hζ.1
  have hI := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero
    (by simp : (2 : ℝ≥0∞)≠⊤) (by norm_num : 1<(2 : ℝ≥0∞)) φ.val φ.property n).1
  have hm := mul_le_mul_of_nonneg_right hζlo hI
  have hnR : 0<(n : ℝ) := by exact_mod_cast (show 0<n by omega)
  apply (le_div_iff₀ (mul_pos Real.pi_pos hnR)).mpr
  rw [he,pow_one]
  nlinarith

end NLS.ZakharovShabat
