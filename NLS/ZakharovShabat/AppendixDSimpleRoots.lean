import NLS.ZakharovShabat.AppendixDSineProducts
import NLS.ZakharovShabat.SingleSpectralProductOrders

/-! # Simple roots of the normalized Appendix D product

Deleting a root leaves a nonvanishing entire factor at that root whenever
it occurs only once. Thus the full product has analytic order one there.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A prescribed root with no other occurrence is a simple zero of the full product. -/
theorem analyticOrderAt_appendixDProduct_of_unique_root (hp : p ≠ ⊤) (a : Coeff p)
    (n : ℤ) (hunique : ∀ k : ℤ, k ≠ n → displacedRoots a n ≠ displacedRoots a k) :
    analyticOrderAt (fun z => appendixDProduct (z,a)) (displacedRoots a n) = 1 := by
  have hd : AnalyticAt ℂ (fun z => appendixDDeletedProduct n (z,a)) (displacedRoots a n) :=
    ((analyticOnNhd_appendixDDeletedProduct hp n) _ (mem_univ _)).comp
      (analyticAt_id.prod analyticAt_const)
  have hf : AnalyticAt ℂ (fun z => singleSpectralFactor (displacedRoots a) z n)
      (displacedRoots a n) := by
    unfold singleSpectralFactor
    exact (analyticAt_const.sub analyticAt_id).div_const
  have he : (fun z => appendixDProduct (z,a)) =
      (fun z => singleSpectralFactor (displacedRoots a) z n) *
      (fun z => appendixDDeletedProduct n (z,a)) := by
    funext z
    exact appendixDProduct_eq_deleted hp n (z,a)
  rw [he, analyticOrderAt_mul hf hd,
    analyticOrderAt_singleSpectralFactor,
    hd.analyticOrderAt_eq_zero.mpr
      (appendixDDeletedProduct_ne_zero_of_off_other hp n _ a hunique)]
  simp

/-- An injective displaced-root sequence gives only simple zeros. -/
theorem analyticOrderAt_appendixDProduct_of_injective (hp : p ≠ ⊤) (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) (n : ℤ) :
    analyticOrderAt (fun z => appendixDProduct (z,a)) (displacedRoots a n) = 1 :=
  analyticOrderAt_appendixDProduct_of_unique_root hp a n
    (fun _ hkn h => hkn (ha h.symm))

/-- The reciprocal of every deleted product is meromorphic on the whole plane. -/
theorem meromorphicAt_inv_appendixDDeletedProduct (hp : p ≠ ⊤) (n : ℤ) (a : Coeff p)
    (z : ℂ) : MeromorphicAt (fun w => (appendixDDeletedProduct n (w,a))⁻¹) z := by
  have h : AnalyticAt ℂ (fun w => appendixDDeletedProduct n (w,a)) z :=
    ((analyticOnNhd_appendixDDeletedProduct hp n) _ (mem_univ _)).comp
      (analyticAt_id.prod analyticAt_const)
  exact h.meromorphicAt.inv

/-- Deleting a different root preserves the simple order at every retained root. -/
theorem analyticOrderAt_appendixDDeletedProduct_of_injective (hp : p ≠ ⊤) (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) (n k : ℤ) (hkn : k ≠ n) :
    analyticOrderAt (fun z => appendixDDeletedProduct n (z,a)) (displacedRoots a k) = 1 := by
  have hd : AnalyticAt ℂ (fun z => appendixDDeletedProduct n (z,a)) (displacedRoots a k) :=
    ((analyticOnNhd_appendixDDeletedProduct hp n) _ (mem_univ _)).comp
      (analyticAt_id.prod analyticAt_const)
  have hf : AnalyticAt ℂ (fun z => singleSpectralFactor (displacedRoots a) z n)
      (displacedRoots a k) := by
    unfold singleSpectralFactor
    exact (analyticAt_const.sub analyticAt_id).div_const
  have he : (fun z => appendixDProduct (z,a)) =
      (fun z => singleSpectralFactor (displacedRoots a) z n) *
      (fun z => appendixDDeletedProduct n (z,a)) := by
    funext z
    exact appendixDProduct_eq_deleted hp n (z,a)
  have h := analyticOrderAt_appendixDProduct_of_injective hp a ha k
  rw [he, analyticOrderAt_mul hf hd,
    analyticOrderAt_singleSpectralFactor] at h
  have hne : displacedRoots a n ≠ displacedRoots a k := fun heq => hkn (ha heq.symm)
  simpa only [if_neg hne, zero_add] using h

/-- For a simple sequence, each retained root is a simple pole of the deleted reciprocal. -/
theorem meromorphicOrderAt_inv_appendixDDeletedProduct_of_injective (hp : p ≠ ⊤)
    (a : Coeff p) (ha : Function.Injective (displacedRoots a)) (n k : ℤ) (hkn : k ≠ n) :
    meromorphicOrderAt (fun z => (appendixDDeletedProduct n (z,a))⁻¹)
      (displacedRoots a k) = -1 := by
  have hd : AnalyticAt ℂ (fun z => appendixDDeletedProduct n (z,a)) (displacedRoots a k) :=
    ((analyticOnNhd_appendixDDeletedProduct hp n) _ (mem_univ _)).comp
      (analyticAt_id.prod analyticAt_const)
  change meromorphicOrderAt ((fun z => appendixDDeletedProduct n (z,a))⁻¹)
    (displacedRoots a k) = -1
  rw [meromorphicOrderAt_inv, hd.meromorphicOrderAt_eq,
    analyticOrderAt_appendixDDeletedProduct_of_injective hp a ha n k hkn]
  simp

end NLS.ZakharovShabat
