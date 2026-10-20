import NLS.ZakharovShabat.WKBLeadingFrequencyCutoff

/-! # Frequency cutoffs for bounded displacements

Bounded spectral shifts alone give a uniform linear lower bound on both tails.
-/

noncomputable section
open Complex
namespace NLS.ZakharovShabat

/-- Bounded displacements alone give a linear frequency lower bound
outside a common cutoff. No inverse-index displacement bound is required. -/
theorem exists_wkb_bounded_frequency_cutoff (D : ℝ) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∀ δ : ℤ → ℂ,
      (∀ n, ‖δ n‖ ≤ D) → ∀ n : ℤ, K ≤ n.natAbs →
        1 ≤ ‖(Real.pi:ℂ)*n+δ n‖ ∧ 1+|(n:ℝ)| ≤ ‖(Real.pi:ℂ)*n+δ n‖ := by
  obtain ⟨K₀,hK₀,hcut⟩ := exists_near_free_frequency_cutoff D hD
  refine ⟨max K₀ 2,hK₀.trans_le (le_max_left _ _),?_⟩
  intro δ hδ n hn
  have hnK := (le_max_left K₀ 2).trans hn
  have hn2 : (2:ℝ) ≤ (n.natAbs:ℝ) := by
    exact_mod_cast (le_max_right K₀ 2).trans hn
  have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
  have hh := (hcut n hnK ((Real.pi:ℂ)*n+δ n)
    (by simpa only [add_sub_cancel_left] using hδ n)).2.2
  have hlinear : 1+|(n:ℝ)| ≤ ‖(Real.pi:ℂ)*n+δ n‖ := by
    rw [habs]
    nlinarith [Real.pi_gt_three]
  exact ⟨by linarith [abs_nonneg (n:ℝ)],hlinear⟩

end NLS.ZakharovShabat
