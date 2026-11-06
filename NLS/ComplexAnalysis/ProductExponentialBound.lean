import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-! # A convergent complex product is bounded by the exponential of its factor-error sum. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
open Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_hasProd_le_exp_sum (f : ℕ → ℂ) (p : ℂ) (a : ℕ → ℝ)
    (hp : HasProd f p) (ha : Summable a) (ha0 : ∀ k, 0 ≤ a k)
    (hf : ∀ k, ‖f k‖ ≤ 1+a k) : ‖p‖ ≤ Real.exp (∑' k, a k) := by
  have ht := continuous_norm.continuousAt.tendsto.comp hp.tendsto_prod_nat
  apply le_of_tendsto ht
  filter_upwards with M
  change ‖∏ k ∈ Finset.range M, f k‖ ≤ _
  rw [norm_prod]
  calc
    _ ≤ ∏ k ∈ Finset.range M, (1+a k) :=
      Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hf k)
    _ ≤ Real.exp (∑ k ∈ Finset.range M, a k) := Real.prod_one_add_le_exp_sum _ ha0
    _ ≤ _ := Real.exp_le_exp.mpr (ha.sum_le_tsum _ (fun k _ => ha0 k))

end NLS.ComplexAnalysis
