import NLS.MKdV.MiuraActionCotangentIndependence

/-! # Global angle transport and regular physical action strata

These are necessary coordinate ingredients for Theorems 3 and 4.
They integrate the already proved angle-action clause on the complete
physical Gardner group. An independent mKdV Birkhoff chart and the
remaining global factorizations are not asserted here.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- The actual single-valued phase exp(2 i theta_m) rotates at the
printed unit angle speed along J_m and is constant along every other
physical action flow, for the entire real time line. -/
theorem theorem4_iii_global_angle_transport (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hangle : miuraMKdVAction a ha m ≠ 0) (t : ℝ) :
    miuraThetaPhase m (scalarInclusion (miuraH1ActionFlow a ha n t)) =
      if m = n then Complex.exp (2*I*(t : ℂ))*miuraThetaPhase m (scalarInclusion a)
      else miuraThetaPhase m (scalarInclusion a) :=
  miuraThetaPhase_miuraActionFlow a ha m n hm hn hangle t

theorem theorem4_action_directions_independent (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    LinearIndependent ℂ
      (fun n : {n : ℕ // 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0} =>
        l2GardnerDirection (miuraL2Action n.val) (scalarInclusion a)) :=
  linearIndependent_miuraGardnerDirections a ha

/-- The original H1 Frechet differentials of the physical action
extensions and the literal mean have no finite linear relation on
their open-action stratum. No condition is imposed on other gaps. -/
theorem theorem4_H1_action_differentials_independent (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j)))
    (S : Finset {n : ℕ // 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0})
    (c : {n : ℕ // 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0} → ℂ) (c₀ : ℂ)
    (hz : c₀ • WeightedCoeff.evalCLM (Weight.sobolev 1) 2 0 +
      ∑ n ∈ S, c n • fderiv ℂ (fun u : ScalarDomain 2 => miuraL2Action n.val (scalarInclusion u)) a = 0) :
    c₀ = 0 ∧ ∀ n ∈ S, c n = 0 :=
  miuraH1ActionCotangent_coefficients_unique a ha S c c₀ hz

end NLS.Articles.MKdVNLSHierarchies
