import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.Complex.Basic

/-! # Passing a uniform exterior-product bound to a symmetric infinite product

The central product is retained multiplicatively, so it may vanish.
-/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

/-- A convergent symmetric product is bounded by its finite central product
and a common bound for all remaining finite products. -/
theorem norm_symmetric_product_limit_le_core (f : ℤ → ℂ) (n : ℤ) (N : ℕ)
    (hn : N ≤ n.natAbs) (q : ℂ) (C : ℝ)
    (hlim : Tendsto (fun K : ℕ => ∏ m ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase n, f m)
      atTop (𝓝 q))
    (hbound : ∀ s : Finset ℤ, n ∉ s → (∀ m ∈ s, N ≤ m.natAbs) → ‖∏ m ∈ s, f m‖ ≤ C) :
    ‖q‖ ≤ C*‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ), f m‖ := by
  classical
  apply le_of_tendsto hlim.norm
  filter_upwards [eventually_ge_atTop N] with K hK
  let s := (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase n
  let c := Finset.Ioo (-(N:ℤ)) (N:ℤ)
  have hc : c ⊆ s := by
    intro m hm
    simp only [c,Finset.mem_Ioo] at hm
    simp only [s,Finset.mem_erase,Finset.mem_Icc]
    constructor
    · intro he; subst m; omega
    · omega
  have hns : n ∉ s \ c := by
    intro h
    exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl
  have hext : ∀ m ∈ s \ c, N ≤ m.natAbs := by
    intro m hm
    have hmc := (Finset.mem_sdiff.mp hm).2
    simp only [c,Finset.mem_Ioo,not_and_or] at hmc
    omega
  have hp := Finset.prod_sdiff (f := f) hc
  change (∏ m ∈ s \ c, f m)*(∏ m ∈ c, f m) = ∏ m ∈ s, f m at hp
  change ‖∏ m ∈ s, f m‖ ≤ C*‖∏ m ∈ c, f m‖
  rw [← hp,norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound (s \ c) hns hext) (norm_nonneg _)

end NLS.ComplexAnalysis
