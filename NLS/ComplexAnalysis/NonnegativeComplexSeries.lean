import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith

/-! # Complex series with eventually nonnegative real terms from partial-sum limits -/

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

theorem hasSum_of_eventually_nonnegative_real_partial_limit (f : ℕ → ℂ) (A : ℂ)
    (hreal : ∀ᶠ k : ℕ in atTop, f k = (‖f k‖ : ℂ))
    (hlim : Tendsto (fun N => ∑ k ∈ Finset.range N, f k) atTop (𝓝 A)) : HasSum f A := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hreal
  have ht := (hlim.comp (tendsto_add_atTop_nat N)).sub_const (∑ k ∈ Finset.range N, f k)
  have he (K : ℕ) : (∑ k ∈ Finset.range (K+N), f k) - (∑ k ∈ Finset.range N, f k) =
      ∑ k ∈ Finset.range K, f (k+N) := by
    rw [Nat.add_comm K N, Finset.sum_range_add]
    simp only [add_comm N]
    abel
  have htail : Tendsto (fun K => ∑ k ∈ Finset.range K, f (k+N)) atTop
      (𝓝 (A - ∑ k ∈ Finset.range N, f k)) := by
    simpa only [Function.comp_def, he] using ht
  have hs : Summable (fun k => f (k+N)) :=
    (hasSum_of_nonnegative_real_partial_limit (fun k => f (k+N)) _ (fun k => hN _ (by omega)) htail).summable
  have hall : Summable f := (summable_nat_add_iff N).mp hs
  have hv : (∑' k, f k) = A := tendsto_nhds_unique hall.hasSum.tendsto_sum_nat hlim
  rw [← hv]
  exact hall.hasSum


end NLS.ComplexAnalysis
