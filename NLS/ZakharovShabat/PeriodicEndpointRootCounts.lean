import NLS.ZakharovShabat.PeriodicEndpointRegions
import NLS.ZakharovShabat.PeriodicProductFamilyLimits
import NLS.ComplexAnalysis.ZeroMultisetRestriction

/-!
# Analytic periodic counts and endpoint multisets

Inside the closed central vertical strip, all spectral roots are central.
Filtering the central endpoint multiset therefore gives the exact analytic
count of the canonical periodic product, with repeated endpoints retained.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The natural analytic order of the periodic product is its original algebraic multiplicity. -/
theorem analyticOrderNatAt_canonicalPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (z : ℂ) :
    analyticOrderNatAt (canonicalPeriodicProduct hp φ) z = periodicAlgebraicMultiplicity hp φ z := by
  unfold analyticOrderNatAt
  rw [analyticOrderAt_canonicalPeriodicProduct hp hp1 φ z]
  rfl

/-- Filtering the central multiset counts precisely the original multiplicities in the selected set. -/
theorem card_filter_centralPeriodicRoots (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (S : Set ℂ) :
    ((centralPeriodicRoots hp φ N).filter (fun z => z ∈ S)).card =
      ∑ z ∈ (centralPeriodicSpectrum hp φ N).filter (fun z => z ∈ S),
        periodicAlgebraicMultiplicity hp φ z := by
  let F : Multiset ℂ →+ ℕ := {
    toFun := fun m => (m.filter (fun z => z ∈ S)).card
    map_zero' := by simp
    map_add' := fun a b => by simp }
  change F (∑ z ∈ centralPeriodicSpectrum hp φ N,
    Multiset.replicate (periodicAlgebraicMultiplicity hp φ z) z) = _
  rw [map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  change ((Multiset.replicate _ z).filter (fun z => z ∈ S)).card = _
  have hf (k : ℕ) : ((Multiset.replicate k z).filter (fun z => z ∈ S)).card =
      if z ∈ S then k else 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      by_cases hz : z ∈ S <;> simp [Multiset.replicate_succ,hz,ih]
  exact hf _

/-- Analytic counts in the central strip equal the cardinality of the filtered original multiset. -/
theorem PeriodicEndpointLabeling.analyticZeroCount_eq_card_filter_roots
    {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : PeriodicEndpointLabeling hp φ N ξ η) (hp1 : 1 < p)
    (S : Set ℂ) (hS : ∀ z ∈ S, |z.re| ≤ centralCircleRadius N) :
    analyticZeroCount (canonicalPeriodicProduct hp φ) S =
      ((centralPeriodicRoots hp φ N).filter (fun z => z ∈ S)).card := by
  rw [card_filter_centralPeriodicRoots]
  rw [analyticZeroCount_eq_sum ((centralPeriodicSpectrum hp φ N).filter (fun z => z ∈ S))
    (fun _ hz => (Finset.mem_filter.mp hz).2) (fun z hz => Finset.mem_filter.mpr
      ⟨h.spectrum_mem_central_of_abs_re_le z ((canonicalPeriodicProduct_eq_zero_iff hp hp1 φ z).mp hz.2)
        (hS z hz.1),hz.1⟩)]
  exact Finset.sum_congr rfl (fun z _ => analyticOrderNatAt_canonicalPeriodicProduct hp hp1 φ z)

/-- The analytic count is the sum of the selected occurrences of both central endpoint slots. -/
theorem PeriodicEndpointLabeling.analyticZeroCount_eq_sum_slots
    {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : PeriodicEndpointLabeling hp φ N ξ η) (hp1 : 1 < p)
    (S : Set ℂ) (hS : ∀ z ∈ S, |z.re| ≤ centralCircleRadius N) :
    analyticZeroCount (canonicalPeriodicProduct hp φ) S =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ((if ξ n ∈ S then 1 else 0) + (if η n ∈ S then 1 else 0) : ℕ) := by
  rw [h.analyticZeroCount_eq_card_filter_roots hp1 S hS, ← h.central.roots]
  let F : Multiset ℂ →+ ℕ := {
    toFun := fun m => (m.filter (fun z => z ∈ S)).card
    map_zero' := by simp
    map_add' := fun a b => by simp }
  change F (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({ξ n,η n} : Multiset ℂ)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  change (({ξ n,η n} : Multiset ℂ).filter (fun z => z ∈ S)).card = _
  by_cases hx : ξ n ∈ S <;> by_cases hy : η n ∈ S <;> simp [Multiset.insert_eq_cons,Multiset.filter_singleton,hx,hy]

end NLS.ZakharovShabat
