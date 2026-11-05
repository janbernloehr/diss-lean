import NLS.MKdV.MiuraFiniteGapAbelianPhase

/-! # Independent Abelian phase construction for the final angle comparison

Every finite partial phase is analytic locally on the exact original
open-action domain, without imposing open conditions on other actions.
For every finite-gap profile this gives the full independent Abelian
series, with proved convergence and independence of the support set.
The general infinite-gap convergence and negative action generators
remain required for the final clause of Theorem 4(iii).
-/
noncomputable section
open Set Complex Filter Topology
open NLS.KdV NLS.MKdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem independent_mKdV_finite_Abelian_phase_analytic (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hJ : miuraMKdVAction a ha n ≠ 0) (F : Finset ℕ)
    {T : Type*} [TopologicalSpace T] (A : T → ScalarDomain 2) (hA : Continuous A)
    (hreal : ∀ t j, (A t).val j = conj ((A t).val (-j))) (t0 : T) (h0 : A t0 = a) :
    ‖miuraFiniteAbelianPhase a ha n hn F‖ = 1 ∧
      ∃ P : ScalarDomain 2 → ℂ, AnalyticAt ℂ P a ∧
        P a = miuraFiniteAbelianPhase a ha n hn F ∧
        ∀ᶠ t in 𝓝 t0, P (A t) = miuraFiniteAbelianPhase (A t) (hreal t) n hn F :=
  ⟨norm_miuraFiniteAbelianPhase a ha n hn hJ F,
    exists_miuraFiniteAbelianPhase_analytic_extension_along_real_family a ha n hn hJ F A hA hreal t0 h0⟩

theorem independent_mKdV_partial_Abelian_phase_original_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hJ : miuraMKdVAction a ha n ≠ 0) (F : Finset ℕ) :
    ∃ P : ScalarDomain 2 → ℂ, AnalyticAt ℂ P a ∧
      P a = miuraFiniteAbelianPhase a ha n hn F ∧
      ∀ᶠ b : {b : ScalarDomain 2 // ∀ j, b.val j = conj (b.val (-j))} in 𝓝 ⟨a,ha⟩,
        P b.val = miuraFiniteAbelianPhase b.val b.property n hn F :=
  exists_miuraFiniteAbelianPhase_original_H1_analytic_extension a ha n hn hJ F

theorem independent_mKdV_finiteGap_Abelian_phase (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (hfg : miuraFiniteGap a ha)
    (n : ℕ) (hn : 1 ≤ n) (hJ : miuraMKdVAction a ha n ≠ 0) :
    ‖miuraFiniteGapAbelianPhase a ha hfg n hn‖ = 1 ∧
      Summable (fun k : ℕ => hillDirichletRegularAbelianTerm (realSobolevMiuraHillPotential a ha)
        n hn (k+1) (by omega)) ∧
      miuraFiniteGapAbelianPhase a ha hfg n hn =
        hillDirichletUnitPhase (realSobolevMiuraHillPotential a ha) n hn*
          exp (I*∑' k : ℕ,hillDirichletRegularAbelianTerm (realSobolevMiuraHillPotential a ha)
            n hn (k+1) (by omega)) :=
  ⟨norm_miuraFiniteGapAbelianPhase a ha hfg n hn hJ,
    miuraFiniteGapAbelian_corrections_summable a ha hfg n hn,
    miuraFiniteGapAbelianPhase_eq_full_series a ha hfg n hn⟩

end NLS.Articles.MKdVNLSHierarchies
