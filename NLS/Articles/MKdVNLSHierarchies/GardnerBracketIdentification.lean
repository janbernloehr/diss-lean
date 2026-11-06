import NLS.MKdV.MiuraAngleActionBracket
import NLS.MKdV.MiuraRestrictedActionBrackets
import NLS.Articles.MKdVNLSHierarchies.AnalyticActionExtension

/-! # Theorem 4(iii)'s angle-action clause and the actual Gardner transfer

The mKdV action is the independent physical Hill contour, extended by
Lemma 7. Its actual L2 gradient has an L2 distribution derivative. The
restricted NLS phase supplies the genuine local angle differential, whose
Gardner bracket is the printed Kronecker delta. Only that angle's own
action must be nonzero. The final mKdV-angle sum factorization is separate.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.Poisson NLS.Fourier NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate SchwartzMap
namespace NLS.Articles.MKdVNLSHierarchies

theorem theorem4_iii_angle_action (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hangle : miuraMKdVAction a ha m ≠ 0) :
    miuraThetaGardnerBracket m n (scalarInclusion a) = if m = n then 1 else 0 :=
  miuraThetaGardnerBracket_of_action_ne_zero a ha m n hm hn hangle

/-- This certifies that the bracket uses Gardner's actual spatial
derivative, represented by an L2 field at every original real H1 input. -/
theorem theorem4_iii_actual_Gardner_derivative (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    miuraL2Action n (scalarInclusion a) = miuraMKdVAction a ha n ∧
      TemperedDistribution.derivCLM ℂ (periodOneL2Distribution (l2ScalarGradient (miuraL2Action n) (scalarInclusion a))) =
        periodOneL2Distribution (l2GardnerDirection (miuraL2Action n) (scalarInclusion a)) :=
  ⟨miuraL2Action_eq_physical a ha n hn,miuraActionGardner_distribution a ha n hn⟩

/-- The action invariance needed before the normal-form factorization
in Theorem 4(ii), with all signed NLS indices and closed action gaps. -/
theorem theorem4_ii_restricted_action_invariance (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    l2GardnerBracket (miuraRestrictedNLSAction m) (miuraL2Action n) (scalarInclusion a) = 0 :=
  miuraRestrictedNLSAction_gardner_commutes a ha m n hn

end NLS.Articles.MKdVNLSHierarchies
