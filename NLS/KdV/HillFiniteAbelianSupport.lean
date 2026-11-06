import NLS.KdV.HillFiniteAbelianPhase

/-! # The finite-gap Abelian phase is independent of the truncation set

Every closed gap has an exactly zero regular correction. Once a finite
set contains all open gaps, its correction sum is the genuine absolutely
convergent series and its phase is independent of any further truncation.
-/
noncomputable section
open Set Complex
open NLS.ZakharovShabat
namespace NLS.KdV

theorem summable_hillDirichletRegularAbelianTerm_of_closed_complement
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ)
    (hclosed : ∀ k, k ∉ F → hillRealGapHalfLength q.val q.property.1 q.property.2 (k+1) = 0) :
    Summable (fun k : ℕ => hillDirichletRegularAbelianTerm q n hn (k+1) (by omega)) := by
  apply summable_of_hasFiniteSupport
  apply F.finite_toSet.subset
  intro k hk
  change hillDirichletRegularAbelianTerm q n hn (k+1) (by omega) ≠ 0 at hk
  by_contra hnot
  exact hk (hillDirichletRegularAbelianTerm_closed q n hn (k+1) (by omega) (hclosed k hnot))

theorem hillFiniteRegularAbelianSum_eq_tsum_of_closed_complement
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ)
    (hclosed : ∀ k, k ∉ F → hillRealGapHalfLength q.val q.property.1 q.property.2 (k+1) = 0) :
    hillFiniteRegularAbelianSum q n hn F =
      ∑' k : ℕ,hillDirichletRegularAbelianTerm q n hn (k+1) (by omega) := by
  exact (tsum_eq_sum (fun k hk =>
    hillDirichletRegularAbelianTerm_closed q n hn (k+1) (by omega) (hclosed k hk))).symm

theorem hillFiniteAbelianPhase_independent_support (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (F G : Finset ℕ)
    (hF : ∀ k, k ∉ F → hillRealGapHalfLength q.val q.property.1 q.property.2 (k+1) = 0)
    (hG : ∀ k, k ∉ G → hillRealGapHalfLength q.val q.property.1 q.property.2 (k+1) = 0) :
    hillFiniteAbelianPhase q n hn F = hillFiniteAbelianPhase q n hn G := by
  rw [hillFiniteAbelianPhase,hillFiniteAbelianPhase,
    hillFiniteRegularAbelianSum_eq_tsum_of_closed_complement q n hn F hF,
    hillFiniteRegularAbelianSum_eq_tsum_of_closed_complement q n hn G hG]

end NLS.KdV
