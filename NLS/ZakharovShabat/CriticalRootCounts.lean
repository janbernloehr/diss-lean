import NLS.ZakharovShabat.CanonicalCriticalStability
import NLS.ComplexAnalysis.ZeroMultisetRestriction

/-!
# Counting critical labels in spectral subsets

Inside a valid central disc, analytic zero counts are exactly counts of
indices. Each repeated critical point contributes all of its occurrences.
This connects Rouché stability with the ordered canonical coordinates.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A critical count inside the central disc is exactly the number of selected labels there. -/
theorem CriticalPointLabeling.analyticZeroCount_eq_card_filter
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
    {N : ℕ} {ξ : ℤ → ℂ} (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (S : Set ℂ) (hS : S ⊆ closedBall 0 (centralCircleRadius N)) :
    analyticZeroCount (deriv (canonicalDiscriminant hp φ)) S =
      ((Finset.Icc (-(N : ℤ)) N).filter (fun n => ξ n ∈ S)).card := by
  rw [analyticZeroCount_subset_eq_card_filter _ hS (hasFiniteSupport_centralCriticalOrder hp hp1 φ hφ N)]
  change ((centralCriticalRoots hp hp1 φ hφ N).filter (fun z => z ∈ S)).card = _
  rw [← h.central]
  let F : Multiset ℂ →+ ℕ := {
    toFun := fun m => (m.filter (fun z => z ∈ S)).card
    map_zero' := by simp
    map_add' := fun a b => by simp only [Multiset.filter_add, Multiset.card_add] }
  change F (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({ξ n} : Multiset ℂ)) = _
  rw [map_sum]
  change (∑ n ∈ Finset.Icc (-(N : ℤ)) N,
    (({ξ n} : Multiset ℂ).filter (fun z => z ∈ S)).card) = _
  simp [Multiset.filter_singleton, apply_ite]

/-- The same count formula applies to the fixed canonical coordinates at any valid cutoff. -/
theorem canonicalCriticalPoints_count_eq_card_filter (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (N : ℕ)
    (hN : CriticalPointLabeling hp hp1 φ hφ N (canonicalCriticalPoints hp hp1 φ hφ))
    (S : Set ℂ) (hS : S ⊆ closedBall 0 (centralCircleRadius N)) :
    analyticZeroCount (deriv (canonicalDiscriminant hp φ)) S =
      ((Finset.Icc (-(N : ℤ)) N).filter (fun n => canonicalCriticalPoints hp hp1 φ hφ n ∈ S)).card :=
  hN.analyticZeroCount_eq_card_filter S hS

end NLS.ZakharovShabat
