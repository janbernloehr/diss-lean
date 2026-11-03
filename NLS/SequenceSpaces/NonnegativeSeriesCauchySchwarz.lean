import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # Cauchy–Schwarz for nonnegative square-summable real sequences. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.SequenceSpaces

theorem nonneg_series_cauchy_schwarz {ι : Type*} (a b : ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (has : Summable (fun k => (a k)^2)) (hbs : Summable (fun k => (b k)^2)) :
    Summable (fun k => a k*b k) ∧
      (∑' k, a k*b k)^2 ≤ (∑' k, (a k)^2)*(∑' k, (b k)^2) := by
  have hA : 0 ≤ ∑' k, (a k)^2 := tsum_nonneg (fun k => sq_nonneg _)
  have hB : 0 ≤ ∑' k, (b k)^2 := tsum_nonneg (fun k => sq_nonneg _)
  have hp (s : Finset ι) : (∑ k ∈ s, a k*b k) ≤
      Real.sqrt ((∑' k, (a k)^2)*(∑' k, (b k)^2)) := by
    apply Real.le_sqrt_of_sq_le
    exact (Finset.sum_mul_sq_le_sq_mul_sq s a b).trans
      (mul_le_mul (has.sum_le_tsum s (fun k _ => sq_nonneg _))
        (hbs.sum_le_tsum s (fun k _ => sq_nonneg _))
        (Finset.sum_nonneg (fun k _ => sq_nonneg _)) hA)
  have hnonneg (k : ι) : 0 ≤ a k*b k := mul_nonneg (ha k) (hb k)
  have hs := summable_of_sum_le hnonneg hp
  refine ⟨hs,?_⟩
  have ht := hs.tsum_le_of_sum_le hp
  have h0 : 0 ≤ ∑' k, a k*b k := tsum_nonneg hnonneg
  have hh := sq_le_sq₀ h0 (Real.sqrt_nonneg ((∑' k, (a k)^2)*(∑' k, (b k)^2)))
  rw [Real.sq_sqrt (mul_nonneg hA hB)] at hh
  exact hh.mpr ht

end NLS.SequenceSpaces
