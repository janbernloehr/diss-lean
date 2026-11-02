import NLS.MKdV.MiuraFiniteRealActionSections

/-! # Real finite action geometry toward the remaining mKdV normal forms

These results supply real-preserving local sections on the full original
real H1 space. The independent global mKdV chart, infinite action-space
factorization and final independent-angle comparison remain separate.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem theorem4_real_finite_action_submersion (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha)) :
    AnalyticAt ℝ (miuraFiniteRealActionCoordinates (⟨a,ha⟩ : MiuraRealH1) S) ⟨a,ha⟩ ∧
      Function.Surjective (fderiv ℝ (miuraFiniteRealActionCoordinates (⟨a,ha⟩ : MiuraRealH1) S) ⟨a,ha⟩) :=
  ⟨analyticAt_miuraFiniteRealActionCoordinates ⟨a,ha⟩ S,surjective_miuraFiniteRealActionDerivative ⟨a,ha⟩ S⟩

theorem theorem4_real_finite_action_sections (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha))
    (U : Set MiuraRealH1) (hU : IsOpen U) (haU : (⟨a,ha⟩ : MiuraRealH1) ∈ U) :
    ∃ g : (Option S → ℝ) → MiuraRealH1, ∃ V : Set (Option S → ℝ),
      IsOpen V ∧ miuraFiniteRealActionCoordinates (⟨a,ha⟩ : MiuraRealH1) S ⟨a,ha⟩ ∈ V ∧
      AnalyticOnNhd ℝ g V ∧ g (miuraFiniteRealActionCoordinates (⟨a,ha⟩ : MiuraRealH1) S ⟨a,ha⟩) = ⟨a,ha⟩ ∧
      MapsTo g V U ∧ ∀ z ∈ V, (g z).val.val 0 = (z none : ℂ) ∧
        ∀ n : S, 0 < z (some n) ∧ miuraMKdVAction (g z).val (g z).property n.val.val = (z (some n) : ℂ) := by
  obtain ⟨R,g,V,_,hVo,hVa,hg,hga,hmem,hrec,_⟩ := exists_miuraFiniteRealAction_section ⟨a,ha⟩ S U hU haU
  exact ⟨g,V,hVo,hVa,hg,hga,hmem,hrec⟩

end NLS.Articles.MKdVNLSHierarchies
