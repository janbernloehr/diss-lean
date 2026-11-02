import NLS.MKdV.MiuraFiniteActionProjection
import NLS.ComplexAnalysis.AnalyticSubmersionSection

/-! # Constructed local holomorphic sections of physical actions and mean

Every finite collection of open physical actions and the mean can be
varied independently in the complex H1 space near an arbitrary original
real H1 input. The actual action extensions, their derivative and the
section are constructed. All omitted gaps may close and the mean may
vanish. This is finite local coordinate geometry, not a global chart.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraFiniteActionCoordinates_base (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha)) :
    miuraFiniteActionCoordinates a ha S a none = a.val 0 ∧
      ∀ n : S, miuraFiniteActionCoordinates a ha S a (some n) = miuraMKdVAction a ha n.val.val := by
  refine ⟨rfl,?_⟩
  intro n
  exact miuraL2Action_eq_physical a ha n.val.val n.val.property.1

theorem exists_miuraFiniteAction_section (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha))
    (U : Set (ScalarDomain 2)) (hU : IsOpen U) (haU : a ∈ U) :
    ∃ R : (Option S → ℂ) →L[ℂ] ScalarDomain 2,
      ∃ g : (Option S → ℂ) → ScalarDomain 2, ∃ V : Set (Option S → ℂ),
        (fderiv ℂ (miuraFiniteActionCoordinates a ha S) a).comp R = ContinuousLinearMap.id ℂ (Option S → ℂ) ∧
        IsOpen V ∧ miuraFiniteActionCoordinates a ha S a ∈ V ∧
        AnalyticOnNhd ℂ g V ∧ g (miuraFiniteActionCoordinates a ha S a) = a ∧ MapsTo g V U ∧
        (∀ z ∈ V, (g z).val 0 = z none ∧
          ∀ n : S, miuraL2Action n.val.val (scalarInclusion (g z)) = z (some n)) ∧
        fderiv ℂ g (miuraFiniteActionCoordinates a ha S a) = R := by
  obtain ⟨R,hR⟩ := exists_miuraFiniteActionDerivative_rightInverse a ha S
  obtain ⟨g,V,hVo,hVa,hg,hga,hmem,hrec,hdg⟩ :=
    NLS.ComplexAnalysis.exists_analytic_section_of_derivative_rightInverse
      (miuraFiniteActionCoordinates a ha S) a (analyticAt_miuraFiniteActionCoordinates a ha S) R hR U hU haU
  refine ⟨R,g,V,hR,hVo,hVa,hg,hga,hmem,?_,hdg⟩
  intro z hz
  have he := hrec z hz
  exact ⟨congrFun he none,fun n => congrFun he (some n)⟩

end NLS.MKdV
