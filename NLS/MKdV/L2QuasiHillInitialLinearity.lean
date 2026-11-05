import NLS.MKdV.L2QuasiHillScalarNontrivial

/-! # Linear dependence of the rough scalar Hill IVP on initial data -/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

theorem l2QuasiHillSolution_smul_initial (u : IntervalL2) (mu c : ℂ) (v : ℂ × ℂ) :
    l2QuasiHillSolution u mu (c • v) = c • l2QuasiHillSolution u mu v := by
  have hc : (ContinuousMap.const _ (c • quasiHillFixedStateInv v) : Curve (ℂ × ℂ)) =
      c • ContinuousMap.const _ (quasiHillFixedStateInv v) := rfl
  simp only [l2QuasiHillSolution,map_smul,l2SolutionCurve_eq_l2SolutionOperator]
  rw [hc,map_smul,map_smul]

theorem l2QuasiHillPosition_smul_initial (u : IntervalL2) (mu c : ℂ) (v : ℂ × ℂ) :
    l2QuasiHillPosition u mu (c • v) = c • l2QuasiHillPosition u mu v := by
  apply ContinuousMap.ext
  intro t
  change (l2QuasiHillSolution u mu (c • v) t).1 = c*(l2QuasiHillSolution u mu v t).1
  rw [l2QuasiHillSolution_smul_initial]
  rfl

theorem l2QuasiHillSolution_add_initial (u : IntervalL2) (mu : ℂ) (v w : ℂ × ℂ) :
    l2QuasiHillSolution u mu (v+w) = l2QuasiHillSolution u mu v+l2QuasiHillSolution u mu w := by
  have hc : (ContinuousMap.const _ (quasiHillFixedStateInv v+quasiHillFixedStateInv w) : Curve (ℂ × ℂ)) =
      ContinuousMap.const _ (quasiHillFixedStateInv v)+ContinuousMap.const _ (quasiHillFixedStateInv w) := rfl
  simp only [l2QuasiHillSolution,map_add,l2SolutionCurve_eq_l2SolutionOperator]
  rw [hc,map_add,map_add]

end NLS.MKdV
