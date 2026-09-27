import NLS.SequenceSpaces.Compact
import NLS.SequenceSpaces.ExponentEmbedding

/-!
# Compact multipliers from finite-exponent coefficients

Every finite-exponent `ℓᵖ` sequence vanishes uniformly outside a
finite set. Viewed as an `ℓ∞` symbol, it therefore defines a compact
diagonal multiplier on `ℓᵖ`. This is the compactness mechanism for the
off-diagonal remainder in the psi Jacobian of Lemma 12.6.
-/

noncomputable section
open Filter Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A finite-`p` coefficient sequence has uniformly small tails. -/
theorem exists_finset_norm_tail_le (hp : p ≠ ⊤)
    (a : Coeff p) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℤ, ∀ n ∉ s, ‖a n‖ ≤ ε := by
  obtain ⟨s,hs⟩ := Metric.tendsto_atTop.mp (tendsto_truncate hp a) ε hε
  have hs' := hs s le_rfl
  rw [dist_eq_norm] at hs'
  refine ⟨s,fun n hn => ?_⟩
  calc
    ‖a n‖ = ‖(truncate s a-a) n‖ := by simp [hn]
    _ ≤ ‖truncate s a-a‖ :=
      lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le Fact.out)) _ n
    _ ≤ ε := hs'.le

/-- The `ℓ∞` image of a finite-`p` sequence has vanishing tails. -/
theorem exponentInclusion_top_vanishing_tails (hp : p ≠ ⊤)
    (a : Coeff p) :
    ∀ ε > (0 : ℝ), ∃ s : Finset ℤ,
      ∀ n ∉ s, ‖(exponentInclusion (le_top : p ≤ ⊤) a) n‖ ≤ ε := by
  intro ε hε
  obtain ⟨s,hs⟩ := exists_finset_norm_tail_le hp a ε hε
  exact ⟨s,fun n hn => by simpa using hs n hn⟩

/-- Pointwise multiplication by an `ℓᵖ` symbol is compact whenever
the exponent is finite. -/
theorem isCompactOperator_multiplier_of_lp (hp : p ≠ ⊤)
    (a : Coeff p) :
    IsCompactOperator
      (multiplierCLM (p := p) (exponentInclusion (le_top : p ≤ ⊤) a)) :=
  isCompactOperator_multiplierCLM _
    (exponentInclusion_top_vanishing_tails hp a)

end NLS.Coeff
