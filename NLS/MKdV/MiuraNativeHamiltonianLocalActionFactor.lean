import NLS.MKdV.MiuraNativeHamiltonianStationarity
import NLS.MKdV.MiuraCartesianInvariantActionDescent
import NLS.MKdV.MiuraNativeActionMeanParameters

/-! # Native physical Hill Hamiltonian action normal forms at every real profile

The normalized action target is boundedly equivalent to the actual
weight-(2s+1) summable physical actions and literal mean. The entire isotropic mean section includes
zero and negative mean without any choice of square root.
-/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

namespace MiuraNativeCartesianChart
variable {s : ℕ} {a : MiuraRealSobolevSource s}

theorem exists_action_factor (C : MiuraNativeCartesianChart s a) :
    ∃ W : Set MiuraPositiveCartesianTarget, ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → ℂ,
      IsOpen W ∧ miuraSobolevNormalizedCartesianMap s a.val ∈ W ∧
        W ⊆ ball (miuraSobolevNormalizedCartesianMap s a.val) C.radius ∧ IsOpen V ∧
        miuraNormalizedNativeActionMeanMap s a.val ∈ V ∧ AnalyticOnNhd ℂ F V ∧
        ∀ z ∈ W, miuraPositiveCartesianActionMean z ∈ V ∧ F (miuraPositiveCartesianActionMean z) = C.hamiltonian z := by
  obtain ⟨W,V,F,hW,haW,hWO,hV,haV,hF,hrec⟩ := exists_local_scalar_miuraCartesian_action_factor
    C.hamiltonian (ball (miuraSobolevNormalizedCartesianMap s a.val) C.radius) isOpen_ball
    C.hamiltonian_analytic C.hamiltonian_rotation_stationary _ (mem_ball_self C.radius_pos)
  rw [miuraNormalizedCartesian_actionMean s a.val a.property] at haV
  exact ⟨W,V,F,hW,haW,hWO,hV,haV,hF,hrec⟩

end MiuraNativeCartesianChart
end NLS.MKdV
