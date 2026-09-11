import NLS.SequenceSpaces.Multiplier
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Compact diagonal multipliers

A bounded symbol whose tails tend uniformly to zero defines a compact operator
on every Banach `lp` coefficient space, including infinity. The proof uses finite
Fourier projections and convergence in operator norm.
-/

open scoped ENNReal
open Filter
noncomputable section

namespace NLS.Coeff

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Finite Fourier projections are compact, as finite sums of rank-one maps. -/
theorem isCompactOperator_truncateCLM (s : Finset ℤ) :
    IsCompactOperator (truncateCLM (p := p) s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : truncateCLM (p := p) ∅ = 0 := by
      apply ContinuousLinearMap.ext
      intro a
      simp
    rw [he]
    exact isCompactOperator_zero
  | @insert n s hn ih =>
    let singleEval : Coeff p →L[ℂ] Coeff p :=
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p n).comp
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n)
    have he : truncateCLM (p := p) (insert n s) = singleEval + truncateCLM s := by
      apply ContinuousLinearMap.ext
      intro a
      change (∑ k ∈ insert n s, lp.single p k (a k)) =
        lp.single p n (a n) + ∑ k ∈ s, lp.single p k (a k)
      exact Finset.sum_insert hn
    rw [he]
    exact ((isCompactOperator_of_locallyCompactSpace_rng
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p n)).comp_clm
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n)).add ih

/-- Uniform control of the omitted symbol controls the operator-norm error. -/
theorem norm_multiplier_cutoff_error_le (m : Coeff ⊤) (s : Finset ℤ)
    {ε : ℝ} (hε : 0 ≤ ε) (hm : ∀ n ∉ s, ‖m n‖ ≤ ε) :
    ‖(truncateCLM s).comp (multiplierCLM (p := p) m) - multiplierCLM m‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro a
  change ‖truncate s (multiplier m a) - multiplier m a‖ ≤ ε * ‖a‖
  have h : ‖truncate s (multiplier m a) - multiplier m a‖ ≤
      ‖(ε : ℂ) • a‖ := by
    apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
    intro n
    change ‖truncate s (multiplier m a) n - multiplier m a n‖ ≤ ‖(ε : ℂ) * a n‖
    by_cases hn : n ∈ s
    · simp only [truncate_apply, if_pos hn, sub_self, norm_zero]
      exact norm_nonneg _
    · simp only [truncate_apply, if_neg hn, zero_sub, norm_neg, multiplier_apply, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
      exact mul_le_mul_of_nonneg_right (hm n hn) (norm_nonneg _)
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε] using h

/-- Finite Fourier cutoffs of a vanishing symbol converge in operator norm. -/
theorem tendsto_multiplier_cutoff (m : Coeff ⊤)
    (hm : ∀ ε > (0 : ℝ), ∃ s : Finset ℤ, ∀ n ∉ s, ‖m n‖ ≤ ε) :
    Tendsto (fun s : Finset ℤ => (truncateCLM s).comp (multiplierCLM (p := p) m))
      atTop (nhds (multiplierCLM m)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := hm (ε / 2) (half_pos hε)
  refine ⟨s, fun t ht => ?_⟩
  rw [dist_eq_norm]
  exact (norm_multiplier_cutoff_error_le m t (half_pos hε).le
    (fun n hn => hs n (fun hns => hn (ht hns)))).trans_lt (half_lt_self hε)

/-- Diagonal multipliers with uniformly vanishing tails are compact. -/
theorem isCompactOperator_multiplierCLM (m : Coeff ⊤)
    (hm : ∀ ε > (0 : ℝ), ∃ s : Finset ℤ, ∀ n ∉ s, ‖m n‖ ≤ ε) :
    IsCompactOperator (multiplierCLM (p := p) m) :=
  isCompactOperator_of_tendsto (tendsto_multiplier_cutoff m hm)
    (Eventually.of_forall fun s => (isCompactOperator_truncateCLM (p := p) s).comp_clm
      (multiplierCLM m))

end NLS.Coeff
