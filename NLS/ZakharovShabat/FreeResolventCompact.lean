import NLS.ZakharovShabat.FreeResolvent
import NLS.SequenceSpaces.Compact
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compactness of the free resolvent

The reciprocal Fourier symbols vanish uniformly outside finite sets. Thus their
finite-rank cutoffs converge in operator norm. This proves the coefficient-space
content of Chapter 1, Lemma 3.2(i), and extends it to every Banach exponent,
including infinity, with the maximum norm on pairs.
-/

open scoped ENNReal
open Filter
noncomputable section

namespace NLS.ZakharovShabat

/-- The reciprocal symbol has uniformly vanishing frequency tails. -/
theorem inverseSymbol_tails (z : ℂ) (hz : z ∉ freeLattice) :
    ∀ ε > (0 : ℝ), ∃ s : Finset ℤ, ∀ n ∉ s, ‖inverseSymbol z hz n‖ ≤ ε := by
  intro ε hε
  have ht := tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Complex.isClosedEmbedding_intCast
  have he := ht.eventually_ge_atTop ((‖z‖ + ε⁻¹) / Real.pi)
  have hf := Filter.eventually_cofinite.mp he
  refine ⟨hf.toFinset, fun n hn => ?_⟩
  have hn' : (‖z‖ + ε⁻¹) / Real.pi ≤ ‖(n : ℂ)‖ := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not, Function.comp_apply] using hn
  have hlarge : ‖z‖ + ε⁻¹ ≤ Real.pi * ‖(n : ℂ)‖ := by
    have := (div_le_iff₀ Real.pi_pos).mp hn'
    nlinarith
  have htriangle : Real.pi * ‖(n : ℂ)‖ ≤ ‖z - (Real.pi : ℂ) * n‖ + ‖z‖ := by
    have h := norm_sub_le (z - (Real.pi : ℂ) * n) z
    simpa [sub_sub_cancel_left, norm_mul, abs_of_pos Real.pi_pos] using h
  have hd : ε⁻¹ ≤ ‖z - (Real.pi : ℂ) * n‖ := by linarith
  change ‖(z - (Real.pi : ℂ) * n)⁻¹‖ ≤ ε
  rw [norm_inv]
  have h := inv_anti₀ (inv_pos.mpr hε) hd
  simpa using h

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Scalar resolvent cutoffs converge in operator norm, not merely pointwise. -/
theorem tendsto_scalarResolvent_cutoff (z : ℂ) (hz : z ∉ freeLattice) :
    Tendsto (fun s : Finset ℤ => (Coeff.truncateCLM s).comp (scalarResolvent (p := p) z hz))
      atTop (nhds (scalarResolvent z hz)) := by
  rw [scalarResolvent_eq_multiplier]
  exact Coeff.tendsto_multiplier_cutoff _ (inverseSymbol_tails z hz)

theorem isCompactOperator_scalarResolvent (z : ℂ) (hz : z ∉ freeLattice) :
    IsCompactOperator (scalarResolvent (p := p) z hz) := by
  rw [scalarResolvent_eq_multiplier]
  exact Coeff.isCompactOperator_multiplierCLM _ (inverseSymbol_tails z hz)

/-- The free resolvent is compact on the pair base space for every Banach exponent. -/
theorem isCompactOperator_freeResolvent (z : ℂ) (hz : z ∉ freeLattice) :
    IsCompactOperator (freeResolvent (p := p) z hz) := by
  let A := -scalarResolvent (p := p) (-z) (neg_notMem_freeLattice hz)
  let B := scalarResolvent (p := p) z hz
  have hA : IsCompactOperator A :=
    (isCompactOperator_scalarResolvent (p := p) (-z) (neg_notMem_freeLattice hz)).neg
  have hB : IsCompactOperator B := isCompactOperator_scalarResolvent z hz
  have h₁ := (hA.comp_clm (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))).clm_comp
    (ContinuousLinearMap.inl ℂ (Coeff p) (Coeff p))
  have h₂ := (hB.comp_clm (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))).clm_comp
    (ContinuousLinearMap.inr ℂ (Coeff p) (Coeff p))
  have he : (freeResolvent z hz : PairSpace p → PairSpace p) =
      (fun a => (A a.1, 0)) + (fun a => (0, B a.2)) := by
    funext a
    rw [freeResolvent_eq_prodMap]
    change (A a.1, B a.2) = (A a.1 + 0, 0 + B a.2)
    simp
  rw [he]
  exact h₁.add h₂

end NLS.ZakharovShabat
