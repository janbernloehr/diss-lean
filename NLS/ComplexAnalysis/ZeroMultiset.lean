import NLS.ComplexAnalysis.AnalyticZeroCount
import Mathlib.Data.Finsupp.Multiset

/-!
# Listing scalar zeros with multiplicity

A finite-support analytic order function determines a multiset of roots.
Its cardinality is the analytic zero count and each point occurs exactly
as often as its analytic order. A count of two therefore gives two roots
with repetition permitted.
-/

noncomputable section
open scoped Classical
namespace NLS.ComplexAnalysis

/-- The multiset determined by the scalar analytic multiplicities on a set. -/
def analyticZeroMultiset (f : ℂ → ℂ) (K : Set ℂ)
    (h : (fun z : ℂ => if z ∈ K then analyticOrderNatAt f z else 0).HasFiniteSupport) : Multiset ℂ :=
  (Finsupp.ofSupportFinite (fun z : ℂ => if z ∈ K then analyticOrderNatAt f z else 0) h).toMultiset

/-- Each point occurs with exactly its analytic multiplicity in the chosen set. -/
theorem count_analyticZeroMultiset (f : ℂ → ℂ) (K : Set ℂ)
    (h : (fun z : ℂ => if z ∈ K then analyticOrderNatAt f z else 0).HasFiniteSupport) (z : ℂ) :
    (analyticZeroMultiset f K h).count z = if z ∈ K then analyticOrderNatAt f z else 0 := by
  rw [analyticZeroMultiset, Finsupp.count_toMultiset]
  rfl

/-- The multiset cardinality is the exact scalar analytic zero count. -/
theorem card_analyticZeroMultiset (f : ℂ → ℂ) (K : Set ℂ)
    (h : (fun z : ℂ => if z ∈ K then analyticOrderNatAt f z else 0).HasFiniteSupport) :
    (analyticZeroMultiset f K h).card = analyticZeroCount f K := by
  rw [analyticZeroMultiset, Finsupp.card_toMultiset]
  unfold Finsupp.sum analyticZeroCount
  symm
  apply finsum_eq_sum_of_support_subset
  intro z hz
  exact Finsupp.mem_support_iff.mpr hz

/-- Every entry is an actual zero lying in the specified set. -/
theorem mem_analyticZeroMultiset_imp (f : ℂ → ℂ) (K : Set ℂ)
    (h : (fun z : ℂ => if z ∈ K then analyticOrderNatAt f z else 0).HasFiniteSupport)
    {z : ℂ} (hz : z ∈ analyticZeroMultiset f K h) : z ∈ K ∧ f z = 0 := by
  have hn := Multiset.count_ne_zero.mpr hz
  rw [count_analyticZeroMultiset] at hn
  exact analyticZeroCount_support_subset f K hn

/-- At a finite-order analytic zero, the natural multiplicity is positive. -/
theorem analyticOrderNatAt_pos_of_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hfinite : analyticOrderAt f z ≠ ⊤) (hz : f z = 0) :
    0 < analyticOrderNatAt f z :=
  ENat.toNat_pos (hf.analyticOrderAt_ne_zero.mpr hz) hfinite

/-- A total analytic count of two gives two roots with their exact multiplicities, allowing coincidence. -/
theorem exists_two_analytic_zeros {f : ℂ → ℂ} {K : Set ℂ}
    (h : (fun z : ℂ => if z ∈ K then analyticOrderNatAt f z else 0).HasFiniteSupport)
    (hc : analyticZeroCount f K = 2) :
    ∃ x ∈ K, ∃ y ∈ K, f x = 0 ∧ f y = 0 ∧
      ∀ z : ℂ, (if z ∈ K then analyticOrderNatAt f z else 0) = ({x,y} : Multiset ℂ).count z := by
  have hm : (analyticZeroMultiset f K h).card = 2 := (card_analyticZeroMultiset f K h).trans hc
  obtain ⟨x,y,he⟩ := Multiset.card_eq_two.mp hm
  have hx := mem_analyticZeroMultiset_imp f K h (z := x) (by rw [he]; simp)
  have hy := mem_analyticZeroMultiset_imp f K h (z := y) (by rw [he]; simp)
  refine ⟨x,hx.1,y,hy.1,hx.2,hy.2,?_⟩
  intro z
  rw [← count_analyticZeroMultiset f K h z, he]

end NLS.ComplexAnalysis
