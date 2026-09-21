import NLS.ZakharovShabat.BoundaryRootRealStrip
import NLS.ComplexAnalysis.ZeroMultisetRestriction

/-! # Exact counts of boundary labels in a central vertical strip
Analytic counts equal finite index counts on every subset of the central
strip, including real-diameter discs extending above the central box.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat.BoundaryRootLabeling
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {b : BoundaryCondition} {hp : p ≠ ⊤}
variable {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace} {N : ℕ} {ξ : ℤ → ℂ}

/-- The analytic count on a central-strip subset counts precisely its labels, including repetitions. -/
theorem analyticZeroCount_eq_card_filter (h : BoundaryRootLabeling b hp φ hφ N ξ)
    (hp1 : 1 < p) (S : Set ℂ) (hS : ∀ z ∈ S, |z.re| ≤ centralCircleRadius N) :
    analyticZeroCount (b.characteristic hp φ hφ) S =
      ((Finset.Icc (-(N : ℤ)) N).filter (fun n => ξ n ∈ S)).card := by
  let F : Multiset ℂ →+ ℕ := {
    toFun := fun m => (m.filter (fun z => z ∈ S)).card
    map_zero' := by simp
    map_add' := fun a c => by simp only [Multiset.filter_add,Multiset.card_add] }
  have he : analyticZeroCount (b.characteristic hp φ hφ) S = F (b.centralRoots hp φ hφ N) := by
    rw [analyticZeroCount_eq_sum ((b.centralSpectrum hp φ hφ N).filter (fun z => z ∈ S))
      (fun z hz => (Finset.mem_filter.mp hz).2) (by
        intro z hz
        have hs := (b.characteristic_eq_zero_iff hp hp1 φ hφ z).mp hz.2
        exact Finset.mem_filter.mpr ⟨(h.mem_centralSpectrum_iff_abs_re_le z hs).mpr (hS z hz.1),hz.1⟩)]
    simp only [BoundaryCondition.centralRoots,map_sum]
    change _ = ∑ z ∈ b.centralSpectrum hp φ hφ N,
      ((Multiset.replicate (b.algebraicMultiplicity hp φ hφ z) z).filter (fun z => z ∈ S)).card
    simp only [b.analyticOrderNatAt_characteristic hp hp1,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    generalize b.algebraicMultiplicity hp φ hφ z = k
    induction k with
    | zero => simp
    | succ k ih =>
      by_cases hz : z ∈ S
      · simp only [if_pos hz,Multiset.replicate_succ,Multiset.filter_cons,Multiset.card_add,Multiset.card_singleton] at ih ⊢
        omega
      · simp only [if_neg hz,Multiset.replicate_succ,Multiset.filter_cons] at ih ⊢
        exact ih
  rw [he,← h.central,map_sum]
  change (∑ n ∈ Finset.Icc (-(N : ℤ)) N, (({ξ n} : Multiset ℂ).filter (fun z => z ∈ S)).card) = _
  simp [Multiset.filter_singleton,apply_ite]

end NLS.ZakharovShabat.BoundaryRootLabeling
