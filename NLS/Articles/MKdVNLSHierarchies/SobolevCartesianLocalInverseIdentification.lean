import NLS.MKdV.MiuraSobolevCartesianLocalInverse

/-! # Native Sobolev Cartesian inverse charts at the free profile

The actual forward maps and their actual derivatives have full Banach
inverse charts near zero at every integer order, including the literal
original H¹ source. Global inverse geometry and Gardner canonicity are
not asserted by these local statements.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

/-- Every actual native free Jacobian is a bounded linear equivalence. -/
theorem native_cartesian_free_jacobian_allSobolev (s : ℕ) :
    ∃ e : ScalarSobolev s ≃L[ℂ] MiuraPositiveSobolevTarget s,
      fderiv ℂ (miuraSobolevPositiveCartesianMap s) 0 = e.toContinuousLinearMap :=
  ⟨miuraSobolevCartesianFreeEquiv s,miuraSobolevCartesianFreeJacobian_eq_equiv s⟩

/-- Full nonlinear native inverse charts H^s <-> h^(s+1/2) times mean,
with exact inverse identities on open Banach neighborhoods of zero. -/
theorem native_cartesian_zero_inverse_allSobolev (s : ℕ) :
    ∃ U : Set (ScalarSobolev s), ∃ V : Set (MiuraPositiveSobolevTarget s),
      IsOpen U ∧ IsOpen V ∧ (0 : ScalarSobolev s) ∈ U ∧ (0 : MiuraPositiveSobolevTarget s) ∈ V ∧
      miuraSobolevPositiveCartesianMap s '' U = V ∧ BijOn (miuraSobolevPositiveCartesianMap s) U V ∧
      ∃ G : MiuraPositiveSobolevTarget s → ScalarSobolev s,
        AnalyticOnNhd ℂ (miuraSobolevPositiveCartesianMap s) U ∧ AnalyticOnNhd ℂ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (miuraSobolevPositiveCartesianMap s a) = a) ∧
        (∀ z ∈ V, G z ∈ U ∧ miuraSobolevPositiveCartesianMap s (G z) = z) :=
  exists_miuraSobolevPositiveCartesian_localInverse_at_zero s

/-- The original physical H¹ scalar space itself has a full complex
analytic inverse chart in the native order-three-halves positive target. -/
theorem physical_cartesian_original_H1_zero_inverse :
    ∃ U : Set (ScalarDomain 2), ∃ V : Set (MiuraPositiveSobolevTarget 1),
      IsOpen U ∧ IsOpen V ∧ (0 : ScalarDomain 2) ∈ U ∧ (0 : MiuraPositiveSobolevTarget 1) ∈ V ∧
      miuraH1PositiveCartesianMap '' U = V ∧ BijOn miuraH1PositiveCartesianMap U V ∧
      ∃ G : MiuraPositiveSobolevTarget 1 → ScalarDomain 2,
        AnalyticOnNhd ℂ miuraH1PositiveCartesianMap U ∧ AnalyticOnNhd ℂ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (miuraH1PositiveCartesianMap a) = a) ∧
        (∀ z ∈ V, G z ∈ U ∧ miuraH1PositiveCartesianMap (G z) = z) :=
  exists_miuraH1PositiveCartesian_localInverse_at_zero

end NLS.Articles.MKdVNLSHierarchies
