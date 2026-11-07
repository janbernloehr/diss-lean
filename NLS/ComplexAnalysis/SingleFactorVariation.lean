import Mathlib.Analysis.Complex.Basic

/-! Varying one affine factor in a finite product gives an affine
product and a division-free restoring identity, even at zero factors. -/
noncomputable section
open scoped Classical
namespace NLS.ComplexAnalysis

theorem finite_product_single_factor_affine {ι : Type*} (s : Finset ι) (i : ι)
    (f : ℂ → ι → ℂ)
    (hother : ∀ z j, j ≠ i → f z j = f 0 j)
    (hi : ∀ z, f z i = f 0 i+z*(f 1 i-f 0 i)) (z : ℂ) :
    (∏ j ∈ s,f z j) = (∏ j ∈ s,f 0 j)+z*((∏ j ∈ s,f 1 j)-(∏ j ∈ s,f 0 j)) := by
  by_cases hmem : i ∈ s
  · have ht (w : ℂ) : (∏ j ∈ s.erase i,f w j) = ∏ j ∈ s.erase i,f 0 j :=
      Finset.prod_congr rfl (fun j hj => hother w j (Finset.ne_of_mem_erase hj))
    rw [← Finset.mul_prod_erase s (f z) hmem,← Finset.mul_prod_erase s (f 0) hmem,
      ← Finset.mul_prod_erase s (f 1) hmem,ht z,ht 1,hi z]
    ring
  · have ht (w : ℂ) : (∏ j ∈ s,f w j) = ∏ j ∈ s,f 0 j :=
      Finset.prod_congr rfl (fun j hj => hother w j (fun h => hmem (h ▸ hj)))
    rw [ht z,ht 1,sub_self,mul_zero,add_zero]

theorem finite_product_single_factor_restore {ι : Type*} (s : Finset ι) (i : ι)
    (f : ℂ → ι → ℂ) (hmem : i ∈ s)
    (hother : ∀ z j, j ≠ i → f z j = f 0 j) :
    f 0 i*((∏ j ∈ s,f 1 j)-(∏ j ∈ s,f 0 j)) =
      (f 1 i-f 0 i)*(∏ j ∈ s,f 0 j) := by
  have ht : (∏ j ∈ s.erase i,f 1 j) = ∏ j ∈ s.erase i,f 0 j :=
    Finset.prod_congr rfl (fun j hj => hother 1 j (Finset.ne_of_mem_erase hj))
  rw [← Finset.mul_prod_erase s (f 0) hmem,← Finset.mul_prod_erase s (f 1) hmem,ht]
  ring

end NLS.ComplexAnalysis
