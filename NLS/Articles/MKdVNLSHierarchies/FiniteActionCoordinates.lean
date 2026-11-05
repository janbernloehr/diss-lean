import NLS.MKdV.MiuraFiniteActionSections

/-! # Finite local physical action coordinates toward the remaining normal forms

The selected physical actions and mean have an actual surjective H1
derivative and constructed local holomorphic sections. The global mKdV
Birkhoff chart and the remaining main normal forms are still separate.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem theorem4_finite_action_submersion (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha)) :
    AnalyticAt ℂ (miuraFiniteActionCoordinates a ha S) a ∧
      Function.Surjective (fderiv ℂ (miuraFiniteActionCoordinates a ha S) a) :=
  ⟨analyticAt_miuraFiniteActionCoordinates a ha S,surjective_miuraFiniteActionDerivative a ha S⟩

/-- The actual physical actions at the base point are the section's
coordinates; nearby complex values are realized by their checked H1
analytic extensions. Every prescribed H1 source neighborhood is allowed. -/
theorem theorem4_finite_action_sections (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha))
    (U : Set (ScalarDomain 2)) (hU : IsOpen U) (haU : a ∈ U) :
    ∃ g : (Option S → ℂ) → ScalarDomain 2, ∃ V : Set (Option S → ℂ),
      IsOpen V ∧ miuraFiniteActionCoordinates a ha S a ∈ V ∧
      AnalyticOnNhd ℂ g V ∧ g (miuraFiniteActionCoordinates a ha S a) = a ∧ MapsTo g V U ∧
      ∀ z ∈ V, (g z).val 0 = z none ∧
        ∀ n : S, miuraL2Action n.val.val (scalarInclusion (g z)) = z (some n) := by
  obtain ⟨R,g,V,_,hVo,hVa,hg,hga,hmem,hrec,_⟩ := exists_miuraFiniteAction_section a ha S U hU haU
  exact ⟨g,V,hVo,hVa,hg,hga,hmem,hrec⟩

end NLS.Articles.MKdVNLSHierarchies
