import NLS.MKdV.MiuraNativeCartesianCharts
import NLS.MKdV.MiuraSobolevNormalizedActionFlow
import NLS.MKdV.MiuraCartesianRealIdentityAt

/-! # Holomorphic rotation stationarity of the independent native Hill Hamiltonians -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV.MiuraNativeCartesianChart
variable {s : ℕ} {a : MiuraRealSobolevSource s}

def hamiltonian (C : MiuraNativeCartesianChart s a) (z : MiuraPositiveCartesianTarget) : ℂ :=
  miuraSpectralHillHamiltonian s (C.inverse z)

theorem hamiltonian_analytic (C : MiuraNativeCartesianChart s a) :
    AnalyticOnNhd ℂ C.hamiltonian (ball (miuraSobolevNormalizedCartesianMap s a.val) C.radius) := fun z hz =>
  (analyticAt_miuraSpectralHillHamiltonian s _).comp (C.inverse_analytic z hz)

theorem hamiltonian_recover (C : MiuraNativeCartesianChart s a) (b : ScalarSobolev s) (hb : b ∈ C.source) :
    C.hamiltonian (miuraSobolevNormalizedCartesianMap s b) = miuraSpectralHillHamiltonian s b := by
  rw [hamiltonian,C.left_inverse b hb]

theorem hamiltonian_rotation_stationary_real (C : MiuraNativeCartesianChart s a)
    (n : ℕ) (hn : 1 ≤ n) (z : MiuraPositiveCartesianTarget)
    (hz : z ∈ ball (miuraSobolevNormalizedCartesianMap s a.val) C.radius)
    (hzreal : z ∈ miuraCartesianRealSubmodule) :
    fderiv ℂ C.hamiltonian z (miuraCartesianActionVector n z) = 0 := by
  have ha := C.inverse_real z hz hzreal
  have hg := C.right_inverse z hz
  exact fderiv_inverse_coordinates_eq_zero_of_orbit
    (miuraSobolevNormalizedCartesianMap s) C.inverse (miuraSpectralHillHamiltonian s) C.source_open C.left_inverse z hg.1
    (miuraActionFlow s (C.inverse z) ha n)
    (continuous_miuraActionFlow s (C.inverse z) ha n).continuousAt
    (miuraActionFlow_zero s (C.inverse z) ha n)
    (fun t => miuraCartesianRotation n t z) (miuraCartesianRotation_zero n z)
    (miuraCartesianActionVector n z) (hasDerivAt_miuraCartesianRotation_zero n z)
    (fun t => by
      have h := miuraSobolevNormalizedCartesianMap_actionFlow s (C.inverse z) ha n hn t
      rwa [hg.2] at h)
    (miuraSpectralHillHamiltonian_allOrders_miuraActionFlow s (C.inverse z) ha n)
    (C.hamiltonian_analytic z hz).differentiableAt

/-- Every modal rotation annihilates the actual holomorphic Hamiltonian
on the entire complex native inverse ball, including all closed actions. -/
theorem hamiltonian_rotation_stationary (C : MiuraNativeCartesianChart s a)
    (n : ℕ) (hn : 1 ≤ n) (z : MiuraPositiveCartesianTarget)
    (hz : z ∈ ball (miuraSobolevNormalizedCartesianMap s a.val) C.radius) :
    fderiv ℂ C.hamiltonian z (miuraCartesianActionVector n z) = 0 := by
  have hA : AnalyticOnNhd ℂ (fun y => fderiv ℂ C.hamiltonian y (miuraCartesianActionVector n y))
      (ball (miuraSobolevNormalizedCartesianMap s a.val) C.radius) :=
    fun y hy => analyticAt_fderiv_apply_clm (C.hamiltonian_analytic y hy) (miuraCartesianActionVector n)
  have h := analytic_cartesian_eq_zero_of_physical_real_at
    (ball (miuraSobolevNormalizedCartesianMap s a.val) C.radius) isOpen_ball isPreconnected_ball
    ⟨_,mem_ball_self C.radius_pos,miuraSobolevNormalizedCartesianMap_real s a⟩ _ hA
    (fun y hy hyr => C.hamiltonian_rotation_stationary_real n hn y hy hyr)
  exact h hz

end NLS.MKdV.MiuraNativeCartesianChart
