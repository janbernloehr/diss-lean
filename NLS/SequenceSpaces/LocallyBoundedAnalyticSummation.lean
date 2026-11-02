import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.SequenceSpaces.LocallyUniformSummation

/-! # Analytic sums from local bounds in ℓ¹

The summands need not have a common pointwise majorant. Local bounds for
their actual ℓ¹ norms suffice, by Banach analyticity of the sequence map.
-/
noncomputable section
open Set Filter Topology
namespace NLS.Coeff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Locally bounded analytic coefficient families have absolutely convergent,
analytic sums, with locally uniform convergence of the symmetric partial sums. -/
theorem analytic_tsum_of_local_one_bounds (f : E → ℤ → ℂ) {U : Set E}
    (hU : IsOpen U) (ha : ∀ n, AnalyticOnNhd ℂ (fun x => f x n) U)
    (hb : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ C : ℝ, ∀ y ∈ V, ∃ b : Coeff 1, (∀ n, b n = f y n) ∧ ‖b‖ ≤ C) :
    (∀ x ∈ U, Summable (fun n => ‖f x n‖)) ∧
      AnalyticOnNhd ℂ (fun x => ∑' n, f x n) U ∧
      TendstoLocallyUniformlyOn
        (fun (N : ℕ) x => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, f x n)
        (fun x => ∑' n, f x n) atTop U := by
  obtain ⟨he, hseq⟩ := analytic_realization_of_local_bounds f hU ha hb
  have hs (x : E) (hx : x ∈ U) : Summable (fun n => ‖f x n‖) := by
    simpa only [he x hx, ENNReal.toReal_one, Real.rpow_one] using
      (lp.memℓp (ofFunctionOrZero 1 (f x))).summable
      (by norm_num : 0 < (1 : ENNReal).toReal)
  have hsum : AnalyticOnNhd ℂ (fun x => ∑' n, f x n) U := by
    intro x hx
    apply ((lp.tsumCLM ℂ ℤ ℂ).comp_analyticOnNhd hseq x hx).congr
    filter_upwards [hU.mem_nhds hx] with y hy
    exact tsum_congr (he y hy)
  refine ⟨hs, hsum, ?_⟩
  have hconv := tendstoLocallyUniformlyOn_sums_of_continuousOn
    (fun x => ofFunctionOrZero 1 (f x)) U hseq.continuousOn
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hconv ⊢
  intro ε hε x hx
  obtain ⟨V, hV, hbound⟩ := hconv ε hε x hx
  refine ⟨V ∩ U, inter_mem hV self_mem_nhdsWithin, hbound.mono ?_⟩
  intro N hN y hy
  simpa only [he y hy.2] using hN y hy.1

end NLS.Coeff
