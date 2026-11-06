import NLS.MKdV.MiuraNativeAbelianPhase

/-! # Full independent Abelian phase on all original real H¹ profiles

This constructs the actual phase from the independent Hill Dirichlet
divisor for arbitrary infinite-gap profiles. Its negative physical-action
rotation, and hence the final angle-sum clause, remain to be proved.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.KdV NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem independent_mKdV_full_Abelian_phase_original_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hJ : miuraMKdVAction a ha n ≠ 0) :
    ‖miuraFullAbelianPhase a ha n hn‖ = 1 ∧
      Summable (fun k : ℕ => hillDirichletRegularAbelianTerm (realSobolevMiuraHillPotential a ha)
        n hn (k+1) (by omega)) ∧
      Tendsto (fun M : ℕ => miuraFiniteAbelianPhase a ha n hn (Finset.range M)) atTop
        (𝓝 (miuraFullAbelianPhase a ha n hn)) :=
  ⟨norm_miuraFullAbelianPhase a ha n hn hJ,miuraFullAbelian_corrections_summable a ha n hn,
    tendsto_hillFiniteAbelianPhase _ n hn⟩

theorem independent_mKdV_full_Abelian_phase_continuous_original_H1 (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (fun a : {a : ScalarDomain 2 // ∀ j, a.val j = conj (a.val (-j))} =>
      miuraFullAbelianPhase a.val a.property n hn) {a | miuraMKdVAction a.val a.property n ≠ 0} :=
  continuousOn_miuraFullAbelianPhase_original_H1 n hn

/-- The actual independent phase satisfies the boundedness and continuity
inputs of the checked full phase-product descent on exactly its domain. -/
theorem independent_mKdV_full_Abelian_phase_native (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (miuraNativeFullAbelianPhase s hs n hn) {a | miuraNativeNLSAngularCoordinate s n a ≠ 0} ∧
      (∀ a, ‖miuraNativeFullAbelianPhase s hs n hn a‖ ≤ 1) ∧
      (∀ a, miuraNativeNLSAngularCoordinate s n a ≠ 0 → ‖miuraNativeFullAbelianPhase s hs n hn a‖ = 1) :=
  ⟨continuousOn_miuraNativeFullAbelianPhase s hs n hn,norm_miuraNativeFullAbelianPhase_le_one s hs n hn,
    norm_miuraNativeFullAbelianPhase s hs n hn⟩

end NLS.Articles.MKdVNLSHierarchies
