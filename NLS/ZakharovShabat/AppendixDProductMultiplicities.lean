import NLS.ZakharovShabat.DisplacedProductOrders
import NLS.ZakharovShabat.AppendixDSimpleRoots

/-! # Multiplicities after deleting a root

The deleted product counts the retained indices in each root fiber.
Its reciprocal has the negative of that count as its meromorphic order.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The deleted product has exactly the multiplicity of its retained root indices. -/
theorem analyticOrderAt_appendixDDeletedProduct (hp : p ≠ ⊤) (n : ℤ) (a : Coeff p) (z : ℂ) :
    analyticOrderAt (fun w => appendixDDeletedProduct n (w,a)) z =
      (((displacedRootIndices a z).erase n).card : ℕ∞) := by
  have hd : AnalyticAt ℂ (fun w => appendixDDeletedProduct n (w,a)) z :=
    ((analyticOnNhd_appendixDDeletedProduct hp n) _ (mem_univ _)).comp
      (analyticAt_id.prod analyticAt_const)
  have hf : AnalyticAt ℂ (fun w => singleSpectralFactor (displacedRoots a) w n) z := by
    unfold singleSpectralFactor
    exact (analyticAt_const.sub analyticAt_id).div_const
  have he : (fun w => appendixDProduct (w,a)) =
      (fun w => singleSpectralFactor (displacedRoots a) w n) *
      (fun w => appendixDDeletedProduct n (w,a)) := by
    funext w
    exact appendixDProduct_eq_deleted hp n (w,a)
  have hsum := analyticOrderAt_appendixDProduct hp a z
  rw [he, analyticOrderAt_mul hf hd, analyticOrderAt_singleSpectralFactor] at hsum
  by_cases hn : displacedRoots a n = z
  · have hc := Finset.card_erase_add_one ((mem_displacedRootIndices a z n).mpr hn)
    have hc' : ((displacedRootIndices a z).card : ℕ∞) =
        1 + (((displacedRootIndices a z).erase n).card : ℕ∞) := by
      exact_mod_cast (by omega : (displacedRootIndices a z).card =
        1 + ((displacedRootIndices a z).erase n).card)
    rw [if_pos hn, hc'] at hsum
    exact ENat.add_right_injective_of_ne_top (by simp : (1:ℕ∞) ≠ ⊤) hsum
  · have hnmem : n ∉ displacedRootIndices a z := by simpa using hn
    simpa only [if_neg hn, zero_add, Finset.erase_eq_of_notMem hnmem] using hsum

/-- Every pole of the deleted reciprocal has exactly the retained multiplicity;
a point with no retained root has order zero. -/
theorem meromorphicOrderAt_inv_appendixDDeletedProduct (hp : p ≠ ⊤) (n : ℤ)
    (a : Coeff p) (z : ℂ) :
    meromorphicOrderAt (fun w => (appendixDDeletedProduct n (w,a))⁻¹) z =
      -((((displacedRootIndices a z).erase n).card : ℤ) : WithTop ℤ) := by
  have hd : AnalyticAt ℂ (fun w => appendixDDeletedProduct n (w,a)) z :=
    ((analyticOnNhd_appendixDDeletedProduct hp n) _ (mem_univ _)).comp
      (analyticAt_id.prod analyticAt_const)
  change meromorphicOrderAt ((fun w => appendixDDeletedProduct n (w,a))⁻¹) z = _
  rw [meromorphicOrderAt_inv, hd.meromorphicOrderAt_eq,
    analyticOrderAt_appendixDDeletedProduct hp n a z]
  simp

/-- The full reciprocal also records every occurrence, with a negative meromorphic order. -/
theorem meromorphicOrderAt_inv_appendixDProduct (hp : p ≠ ⊤) (a : Coeff p) (z : ℂ) :
    meromorphicOrderAt (fun w => (appendixDProduct (w,a))⁻¹) z =
      -(((displacedRootIndices a z).card : ℤ) : WithTop ℤ) := by
  have hf : AnalyticAt ℂ (fun w => appendixDProduct (w,a)) z :=
    ((analyticOnNhd_appendixDProduct hp) _ (mem_univ _)).comp
      (analyticAt_id.prod analyticAt_const)
  change meromorphicOrderAt ((fun w => appendixDProduct (w,a))⁻¹) z = _
  rw [meromorphicOrderAt_inv, hf.meromorphicOrderAt_eq, analyticOrderAt_appendixDProduct hp a z]
  simp

/-- Away from retained roots, the literal reciprocal products printed in D.4
converge to the reciprocal of the entire deleted product. -/
theorem tendsto_inv_appendixDDeletedProduct (hp : p ≠ ⊤) (n : ℤ) (a : Coeff p) (z : ℂ)
    (hother : ∀ k : ℤ, k ≠ n → z ≠ displacedRoots a k) :
    Tendsto (fun N : ℕ => -∏ m ∈ (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase n,
      singleSpectralDenominator m/(displacedRoots a m-z)) atTop
      (𝓝 ((appendixDDeletedProduct n (z,a))⁻¹)) := by
  have h := (tendsto_appendixDDeletedProduct hp n (z,a)).inv₀
    (appendixDDeletedProduct_ne_zero_of_off_other hp n z a hother)
  simpa only [inv_neg, ← Finset.prod_inv_distrib, inv_div] using h

end NLS.ZakharovShabat
