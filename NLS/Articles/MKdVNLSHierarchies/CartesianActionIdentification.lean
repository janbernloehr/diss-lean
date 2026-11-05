import NLS.MKdV.MiuraL2CartesianCoordinates

/-! # Original-domain Cartesian representatives of the physical mKdV actions

These are selected-coordinate regularity and radius statements. An
independent infinite mKdV inverse chart and Gardner canonicity still
require proof; no such chart is assumed in these constructions.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- Every positive physical action has Cartesian representatives analytic
in the original complex L² topology through any closed selected gap. -/
theorem physical_action_cartesian_original_L2_analytic
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (hn : 1 ≤ n) :
    AnalyticAt ℂ (miuraL2CartesianCoordinates n) a :=
  analyticAt_miuraL2CartesianCoordinates a ha n hn

/-- The radius is the independent original-H¹ physical action, with the
same factor two as ordinary Cartesian action variables. -/
theorem physical_action_cartesian_original_H1_radius
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ((miuraL2CartesianCoordinates n (scalarInclusion a)).1)^2 +
      ((miuraL2CartesianCoordinates n (scalarInclusion a)).2)^2 = 2*miuraMKdVAction a ha n :=
  miuraL2CartesianCoordinates_physical_H1_radius a ha n hn

/-- A closed physical action collapses exactly the corresponding pair;
zero mean and all other closed actions are allowed. -/
theorem physical_action_cartesian_original_H1_closed_iff
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    miuraL2CartesianCoordinates n (scalarInclusion a) = 0 ↔ miuraMKdVAction a ha n = 0 := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  rw [miuraL2CartesianCoordinates_eq_zero_iff_action_zero _ har n hn,miuraL2Action_eq_physical a ha n hn]

end NLS.Articles.MKdVNLSHierarchies
