import NLS.ZakharovShabat.SourceBoundaryWeightedDisplacement

/-! # A common cutoff for the leading frequency estimates

Bounded shifts with an inverse-index budget admit a uniform cutoff on both signed tails with small displacement and a linear frequency lower bound.
-/

noncomputable section
open Complex
namespace NLS.ZakharovShabat

/-- One cutoff makes every bounded, inverse-index displaced frequency
large enough for the sharp WKB multipliers, on both signed tails. -/
theorem exists_wkb_leading_frequency_cutoff (D M : ℝ) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∀ δ : ℤ → ℂ,
      (∀ n, ‖δ n‖ ≤ D) → (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) →
      ∀ n : ℤ, K ≤ n.natAbs →
        ‖δ n‖ ≤ 1 ∧ 1+|(n:ℝ)| ≤ ‖(Real.pi:ℂ)*n+δ n‖ := by
  obtain ⟨K₀,hK₀,hcut⟩ := exists_near_free_frequency_cutoff D hD
  obtain ⟨L,hL⟩ := exists_nat_ge M
  refine ⟨max K₀ (max 2 L),hK₀.trans_le (le_max_left _ _),?_⟩
  intro δ hδ hδM n hn
  have hnK := (le_max_left K₀ (max 2 L)).trans hn
  have hn2 : (2:ℝ) ≤ (n.natAbs:ℝ) := by
    exact_mod_cast ((le_max_left 2 L).trans ((le_max_right K₀ (max 2 L)).trans hn))
  have hnL : (L:ℝ) ≤ (n.natAbs:ℝ) := by
    exact_mod_cast ((le_max_right 2 L).trans ((le_max_right K₀ (max 2 L)).trans hn))
  have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
  have hh := (hcut n hnK ((Real.pi:ℂ)*n+δ n) (by simpa only [add_sub_cancel_left] using hδ n)).2.2
  constructor
  · have hbound := hδM n
    rw [habs] at hbound
    have hpos : (0:ℝ) < 1+n.natAbs := by positivity
    have ht : ‖δ n‖ ≤ M/(1+n.natAbs) := (le_div_iff₀ hpos).mpr (by nlinarith [hbound])
    exact ht.trans ((div_le_one hpos).mpr (by linarith))
  · rw [habs]
    nlinarith [Real.pi_gt_three]

end NLS.ZakharovShabat
