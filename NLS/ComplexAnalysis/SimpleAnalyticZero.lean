import NLS.ComplexAnalysis.ZeroMultiset

/-!
# A count of one gives a unique simple analytic zero

The finite-support zero multiset first supplies a root with natural order one.
Analyticity and finite orders exclude additional zeros hidden by natural-order
conversion, yielding uniqueness among all zeros in the specified set.
-/

noncomputable section
open scoped Classical
namespace NLS.ComplexAnalysis

/-- A count of one gives a single root with its exact multiplicity function. -/
theorem exists_one_analytic_zero {f : ℂ → ℂ} {K : Set ℂ}
    (h : (fun z : ℂ => if z ∈ K then analyticOrderNatAt f z else 0).HasFiniteSupport)
    (hc : analyticZeroCount f K = 1) :
    ∃ x ∈ K, f x = 0 ∧
      ∀ z : ℂ, (if z ∈ K then analyticOrderNatAt f z else 0) = if z = x then 1 else 0 := by
  have hm : (analyticZeroMultiset f K h).card = 1 := (card_analyticZeroMultiset f K h).trans hc
  obtain ⟨x, he⟩ := Multiset.card_eq_one.mp hm
  have hx := mem_analyticZeroMultiset_imp f K h (z := x) (by rw [he]; simp)
  refine ⟨x, hx.1, hx.2, ?_⟩
  intro z
  rw [← count_analyticZeroMultiset f K h z, he]
  simp only [Multiset.count_singleton]

/-- When all zero orders are finite, count one gives exactly one simple zero. -/
theorem exists_unique_simple_analytic_zero {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) (ho : ∀ z ∈ K, analyticOrderAt f z ≠ ⊤)
    (hfin : (K ∩ {z | f z = 0}).Finite) (hc : analyticZeroCount f K = 1) :
    ∃ x ∈ K, f x = 0 ∧ analyticOrderAt f x = 1 ∧ ∀ z ∈ K, f z = 0 ↔ z = x := by
  have hs := hfin.subset (analyticZeroCount_support_subset f K)
  obtain ⟨x, hx, hx0, hm⟩ := exists_one_analytic_zero hs hc
  have hxord : analyticOrderNatAt f x = 1 := by simpa [hx] using hm x
  have he : analyticOrderAt f x = 1 := by
    have h := congrArg (fun n : ℕ => (n : ℕ∞)) hxord
    simpa only [Nat.cast_analyticOrderNatAt (ho x hx), Nat.cast_one] using h
  refine ⟨x, hx, hx0, he, ?_⟩
  intro z hz
  constructor
  · intro hz0
    have hp := analyticOrderNatAt_pos_of_zero (hf z hz) (ho z hz) hz0
    have hmz := hm z
    rw [if_pos hz] at hmz
    by_contra hzx
    rw [if_neg hzx] at hmz
    omega
  · rintro rfl
    exact hx0

end NLS.ComplexAnalysis
