import NLS.MKdV.MiuraActionFlowUniqueness

/-! # Complete physical action flows toward the remaining normal forms

This constructs the actual commuting Gardner circle actions on the
original real H1 phase space. It supplies action-angle machinery needed
by Theorems 3 and 4(ii)-(iii); the independent Birkhoff chart and the
remaining analytic factorizations are not asserted by these flow results.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem theorem4_complete_action_flows (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    Continuous (miuraH1ActionFlow a ha n) ∧
      Function.Periodic (miuraH1ActionFlow a ha n) (2*Real.pi) ∧
      (∀ t j, (miuraH1ActionFlow a ha n t).val j = conj ((miuraH1ActionFlow a ha n t).val (-j))) ∧
      (∀ t, HasDerivAt (fun r => scalarInclusion (miuraH1ActionFlow a ha n r))
        (l2GardnerDirection (miuraL2Action n) (scalarInclusion (miuraH1ActionFlow a ha n t))) t) ∧
      (∀ t (m : ℕ) (_hm : 1 ≤ m),
        miuraMKdVAction (miuraH1ActionFlow a ha n t) (miuraH1ActionFlow_real a ha n t) m = miuraMKdVAction a ha m) ∧
      (∀ t m, miuraNLSAction (miuraH1ActionFlow a ha n t) m = miuraNLSAction a m) ∧
      ∀ t, (miuraH1ActionFlow a ha n t).val 0 = a.val 0 :=
  ⟨continuous_miuraH1ActionFlow a ha n,miuraH1ActionFlow_periodic a ha n,
    miuraH1ActionFlow_real a ha n,hasDerivAt_miuraH1ActionFlow_Gardner a ha n hn,
    fun t m hm => miuraMKdVAction_miuraActionFlow a ha n m hm t,
    miuraNLSAction_miuraActionFlow a ha n,miuraActionFlow_mean a ha n⟩

theorem theorem4_action_flow_commutation (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (t u : ℝ) :
    miuraH1ActionFlow (miuraH1ActionFlow a ha m t) (miuraH1ActionFlow_real a ha m t) n u =
      miuraH1ActionFlow (miuraH1ActionFlow a ha n u) (miuraH1ActionFlow_real a ha n u) m t :=
  miuraH1ActionFlow_comm a ha m n t u

theorem theorem4_closed_action_flow (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hzero : miuraMKdVAction a ha n = 0) (t : ℝ) : miuraH1ActionFlow a ha n t = a :=
  miuraH1ActionFlow_eq_self_of_action_zero a ha n hn hzero t

end NLS.Articles.MKdVNLSHierarchies
