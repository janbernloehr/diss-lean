import NLS.MKdV.MiuraGeneralNLSActionsCartesianChart
import NLS.MKdV.MiuraCartesianRealIdentityAt

/-! # Whole-sequence holomorphic rotation stationarity of the actual NLS actions

Conservation on the complete physical L² action orbit first gives the
stationarity identity on the genuine real Cartesian slice. Holomorphic
uniqueness extends it to the whole common complex inverse target ball around each physical basepoint.
The radius is independent of the selected action index, and all original
signed NLS actions are treated simultaneously in the summable norm.
-/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV.MiuraGeneralCartesianNLSActionChart
variable {a : MiuraRealL2}

theorem observables_rotation_stationary_real (C : MiuraGeneralCartesianNLSActionChart a)
    (n : ℕ) (hn : 1 ≤ n) (z : MiuraPositiveCartesianTarget) (hz : z ∈ ball (miuraPositiveCartesianMap a.val) C.radius)
    (hzreal : z ∈ miuraCartesianRealSubmodule) :
    fderiv ℂ C.observables z (miuraCartesianActionVector n z) = 0 := by
  have ha := C.inverse_real z hz hzreal
  have hg := C.right_inverse z hz
  exact fderiv_inverse_coordinates_eq_zero_of_orbit
    miuraPositiveCartesianMap C.inverse miuraOriginalNLSActionSequence C.source_open C.left_inverse z hg.1
    (miuraOriginalL2ActionFlow (C.inverse z) ha n)
    (continuous_miuraOriginalL2ActionFlow (C.inverse z) ha n).continuousAt
    (miuraOriginalL2ActionFlow_zero (C.inverse z) ha n)
    (fun t => miuraCartesianRotation n t z) (miuraCartesianRotation_zero n z)
    (miuraCartesianActionVector n z) (hasDerivAt_miuraCartesianRotation_zero n z)
    (fun t => by
      have h := miuraPositiveCartesianMap_originalActionFlow (C.inverse z) ha n hn t
      rwa [hg.2] at h)
    (miuraOriginalNLSActionSequence_actionFlow (C.inverse z) ha n)
    (C.observables_analytic z hz).differentiableAt

/-- The entire original l1 action sequence is stationary in every
positive Cartesian rotation direction on one full complex neighborhood.
No nonzero action, finite-gap, or real-input restriction is needed. -/
theorem observables_rotation_stationary (C : MiuraGeneralCartesianNLSActionChart a)
    (n : ℕ) (hn : 1 ≤ n) (z : MiuraPositiveCartesianTarget) (hz : z ∈ ball (miuraPositiveCartesianMap a.val) C.radius) :
    fderiv ℂ C.observables z (miuraCartesianActionVector n z) = 0 := by
  have hA : AnalyticOnNhd ℂ (fun y => fderiv ℂ C.observables y (miuraCartesianActionVector n y))
      (ball (miuraPositiveCartesianMap a.val) C.radius) :=
    fun y hy => analyticAt_fderiv_apply_clm (C.observables_analytic y hy) (miuraCartesianActionVector n)
  have h := analytic_cartesian_eq_zero_of_physical_real_at (ball (miuraPositiveCartesianMap a.val) C.radius) isOpen_ball isPreconnected_ball
    ⟨miuraPositiveCartesianMap a.val,mem_ball_self C.radius_pos,miuraPositiveCartesianMap_physicalReal a⟩ _ hA (fun y hy hyr => C.observables_rotation_stationary_real n hn y hy hyr)
  exact h hz

end NLS.MKdV.MiuraGeneralCartesianNLSActionChart
