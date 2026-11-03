import NLS.MKdV.MiuraSobolevCartesianAnalyticInverse
import NLS.MKdV.MiuraNativeHamiltonianActionFlow

/-! # Native analytic coordinates and action conservation toward Theorem 3

These are necessary dependencies of the frequency comparison. They do
not assert the remaining action normal form, canonical angle construction,
or equality of independent mKdV and restricted NLS frequencies.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- At every positive native Sobolev order the actual physical Cartesian
bijection is a homeomorphism with real analytic forward and inverse maps. -/
theorem physical_native_Cartesian_analytic_homeomorph (s : ℕ) (hs : 1 ≤ s) :
    ∃ e : MiuraRealSobolevSource s ≃ₜ MiuraRealSobolevCartesianTarget s,
      (e : MiuraRealSobolevSource s → MiuraRealSobolevCartesianTarget s) = miuraPhysicalSobolevCartesianMap s ∧
      AnalyticOnNhd ℝ e univ ∧ AnalyticOnNhd ℝ e.symm univ := by
  refine ⟨miuraPhysicalSobolevCartesianHomeomorph s hs,rfl,?_,?_⟩
  · intro a _
    exact analyticAt_miuraPhysicalSobolevCartesianMap s a
  · exact analyticOnNhd_miuraPhysicalSobolevCartesianInverse s hs

/-- K_m, m>=2, is analytic in the actual native Cartesian variables of
order m-1/2 and the literal signed mean on its full real H^(m-1) domain. -/
theorem physical_native_Hill_hamiltonian_Cartesian_representation (m : ℕ) (hm : 2 ≤ m) :
    ∃ F : MiuraRealSobolevCartesianTarget (m-1) → ℂ,
      AnalyticOnNhd ℝ F univ ∧ ∀ a : MiuraRealSobolevSource (m-1),
        F (miuraPhysicalSobolevCartesianMap (m-1) a) = miuraSpectralHillHamiltonian (m-1) a.val := by
  have hs : 1 ≤ m-1 := by omega
  exact ⟨miuraSpectralCartesianHamiltonian (m-1) hs,
    analyticOnNhd_miuraSpectralCartesianHamiltonian (m-1) hs,
    miuraSpectralCartesianHamiltonian_map (m-1) hs⟩

/-- Every K_m is constant along every complete original physical action
flow on its full real H^(m-1) domain, including m=1, closed actions and
zero mean. The actions and flows are the independently identified ones. -/
theorem physical_native_Hill_hamiltonian_action_flow_conservation (m : ℕ) (_hm : 1 ≤ m)
    (a : ScalarSobolev (m-1)) (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (_hn : 1 ≤ n) (t : ℝ) :
    miuraSpectralHillHamiltonian (m-1) (miuraActionFlow (m-1) a ha n t) =
      miuraSpectralHillHamiltonian (m-1) a := by
  exact miuraSpectralHillHamiltonian_allOrders_miuraActionFlow (m-1) a ha n t

end NLS.Articles.MKdVNLSHierarchies
