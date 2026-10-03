import NLS.SequenceSpaces.Truncation

/-! # Uniform tails for coefficientwise dominated families

A single majorant in a finite-exponent sequence space makes the Fourier
tails of every dominated sequence uniformly small in that same norm.
-/

noncomputable section
open Filter
open scoped ENNReal Topology
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coordinate domination is preserved after removing any finite set. -/
theorem norm_sub_truncate_le_of_majorant (a b : Coeff p)
    (h : ∀ n : ℤ, ‖a n‖ ≤ ‖b n‖) (s : Finset ℤ) :
    ‖a-truncate s a‖ ≤ ‖b-truncate s b‖ := by
  apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le Fact.out))
  intro n
  by_cases hn : n ∈ s
  · simp [truncate_apply,hn]
  · simpa [truncate_apply,hn] using h n

/-- One finite cutoff works for every sequence dominated by the same
finite-exponent majorant, and every larger cutoff works as well. -/
theorem eventually_small_tails_of_majorant (hp : p ≠ ⊤) (b : Coeff p)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s : Finset ℤ in atTop, ∀ a : Coeff p,
      (∀ n : ℤ, ‖a n‖ ≤ ‖b n‖) → ‖a-truncate s a‖ < ε := by
  have ht : Tendsto (fun s : Finset ℤ => ‖b-truncate s b‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := b)).sub (tendsto_truncate hp b)).norm
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with s hs a ha
  exact (norm_sub_truncate_le_of_majorant a b ha s).trans_lt hs

end NLS.Coeff
