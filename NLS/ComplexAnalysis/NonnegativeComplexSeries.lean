import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith

/-! # A complex series of nonnegative real terms from its partial-sum limit -/

noncomputable section
open Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem hasSum_of_nonnegative_real_partial_limit (f : ℕ → ℂ) (A : ℂ)
    (hreal : ∀ k, f k = (‖f k‖ : ℂ))
    (hlim : Tendsto (fun N => ∑ k ∈ Finset.range N, f k) atTop (𝓝 A)) : HasSum f A := by
  have hsum (N : ℕ) : (∑ k ∈ Finset.range N, f k).re = ∑ k ∈ Finset.range N, ‖f k‖ := by
    change reCLM (∑ k ∈ Finset.range N, f k) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    have h := congrArg Complex.re (hreal k)
    simpa only [reCLM_apply, ofReal_re] using h
  have hRe : Tendsto (fun N => ∑ k ∈ Finset.range N, ‖f k‖) atTop (𝓝 A.re) := by
    simpa only [Function.comp_def, hsum] using continuous_re.continuousAt.tendsto.comp hlim
  have hsNorm : Summable (fun k => ‖f k‖) := by
    apply (summable_iff_not_tendsto_nat_atTop_of_nonneg (fun k => norm_nonneg (f k))).mpr
    intro hinfty
    have hlo := hinfty.eventually_ge_atTop (A.re+2)
    have hhi := hRe.eventually (gt_mem_nhds (show A.re < A.re+1 by linarith))
    obtain ⟨N, hNlo, hNhi⟩ := (hlo.and hhi).exists
    linarith
  have hs : Summable f := hsNorm.of_norm
  have he : (∑' k, f k) = A := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim
  rw [← he]
  exact hs.hasSum

end NLS.ComplexAnalysis
