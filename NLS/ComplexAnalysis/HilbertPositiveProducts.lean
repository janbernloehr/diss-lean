import NLS.ComplexAnalysis.HilbertWeightedProduct

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ComplexAnalysis



theorem hilbertWeightedProduct_eq_positive_tprod (b a : Coeff 2)
    (hb : ∀ m : ℤ, m ≤ 0 → b m = 0) :
    hilbertWeightedProduct b a =
      ∏' k : ℕ, (1+a ((k+1 : ℕ) : ℤ)*b ((k+1 : ℕ) : ℤ)) := by
  have hi : Function.Injective (fun k : ℕ => ((k+1 : ℕ) : ℤ)) := by
    intro k j h
    change ((k+1 : ℕ) : ℤ) = ((j+1 : ℕ) : ℤ) at h
    omega
  unfold hilbertWeightedProduct
  symm
  convert! (hi.tprod_eq (f := fun m : ℤ => 1+a m*b m) ?_) using 1
  intro m hm
  change (1+a m*b m) ≠ 1 at hm
  have hp : 0 < m := by
    by_contra h
    apply hm
    rw [hb m (by omega : m ≤ 0),mul_zero,add_zero]
  refine ⟨m.toNat-1,?_⟩
  change (((m.toNat-1)+1 : ℕ) : ℤ) = m
  omega

theorem multipliable_positive_hilbertWeightedFactors (b a : Coeff 2) :
    Multipliable (fun j : ℕ => (1+a ((j+1 : ℕ) : ℤ)*b ((j+1 : ℕ) : ℤ))) := by
  have hi : Function.Injective (fun j : ℕ => ((j+1 : ℕ) : ℤ)) := by
    intro j i h
    change ((j+1 : ℕ) : ℤ) = ((i+1 : ℕ) : ℤ) at h
    omega
  have h := (summable_norm_hilbertProductInput b a).comp_injective hi
  apply multipliable_one_add_of_summable
  convert! h using 1

theorem hilbertWeightedProduct_zero (b : Coeff 2) : hilbertWeightedProduct b 0 = 1 := by
  simp [hilbertWeightedProduct]

end NLS.ComplexAnalysis
