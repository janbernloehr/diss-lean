import NLS.SequenceSpaces.FourierTail

/-! # Coordinate decay at finite Banach exponents
Norm convergence of symmetric Fourier tails gives a two-sided cutoff for
all coordinates. This is a fixed-sequence statement, not a uniform bound
on an lp ball.
-/

open Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every finite-exponent coefficient sequence is small outside a finite signed interval. -/
theorem exists_cutoff_norm_apply_lt (hp : p ≠ ⊤) (a : Coeff p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs → ‖a n‖ < ε := by
  have ht : Tendsto (fun N => ‖fourierTail N a‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using (tendsto_fourierTail hp a).norm
  have h := ht.eventually_lt_const hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  refine ⟨N,fun n hn => ?_⟩
  have he := lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    (fourierTail N a) n
  rw [fourierTail_apply,if_pos hn] at he
  exact he.trans_lt (hN N le_rfl)

end NLS.Coeff
