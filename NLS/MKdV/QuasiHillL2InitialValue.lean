import NLS.MKdV.QuasiHillL2WeakSolution

/-! Bounded linear dependence of the actual rough quasi-Hill solution on
its full initial position and quasi-derivative. -/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

/-- The actual scalar IVP as a bounded complex-linear map of initial data. -/
def quasiHillL2InitialMap (u : Coeff 2) (lambda : ℂ) :
    (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) :=
  (ContinuousLinearMap.compLeftContinuous ℂ (Icc (0:ℝ) 1) quasiHillEnergyStateMap).comp
    ((l2SolutionOperator (-(lambda+1)/2,sourcePhysicalL2 (quasiHillEnergySource u lambda))).comp
      ((ContinuousLinearMap.const ℂ (Icc (0:ℝ) 1)).comp quasiHillEnergyInverseStateMap))

theorem quasiHillL2InitialMap_apply (u : Coeff 2) (lambda : ℂ) (v : ℂ × ℂ) :
    quasiHillL2InitialMap u lambda v = quasiHillL2SolutionCurve u lambda v := by
  change ContinuousLinearMap.compLeftContinuous ℂ (Icc (0:ℝ) 1) quasiHillEnergyStateMap
    (l2SolutionOperator _ (ContinuousMap.const _ (quasiHillEnergyInverseStateMap v))) = _
  rw [quasiHillEnergyInverseStateMap_apply,← l2SolutionCurve_eq_l2SolutionOperator]
  rfl

theorem quasiHillL2SolutionCurve_smul (u : Coeff 2) (lambda c : ℂ) (v : ℂ × ℂ) :
    quasiHillL2SolutionCurve u lambda (c • v) = c • quasiHillL2SolutionCurve u lambda v := by
  simp only [← quasiHillL2InitialMap_apply,map_smul]

theorem quasiHillL2SolutionCurve_add (u : Coeff 2) (lambda : ℂ) (v w : ℂ × ℂ) :
    quasiHillL2SolutionCurve u lambda (v+w) =
      quasiHillL2SolutionCurve u lambda v+quasiHillL2SolutionCurve u lambda w := by
  simp only [← quasiHillL2InitialMap_apply,map_add]

theorem quasiHillL2SolutionCurve_zero_initial (u : Coeff 2) (lambda : ℂ) :
    quasiHillL2SolutionCurve u lambda 0 = 0 := by
  simp only [← quasiHillL2InitialMap_apply,map_zero]

/-- No nonzero initial state is lost by the rough IVP construction. -/
theorem quasiHillL2SolutionCurve_injective (u : Coeff 2) (lambda : ℂ) :
    Function.Injective (quasiHillL2SolutionCurve u lambda) := by
  intro v w h
  have he := congrArg (fun f : Curve (ℂ × ℂ) => f ⟨0,by constructor <;> norm_num⟩) h
  simpa only [quasiHillL2SolutionCurve_zero] using he

/-- The normalized scalar Dirichlet column is always a nonzero state. -/
theorem quasiHillL2Dirichlet_state_ne_zero (u : Coeff 2) (lambda : ℂ) :
    quasiHillL2SolutionCurve u lambda (0,1) ≠ 0 := by
  intro h
  have he := (quasiHillL2SolutionCurve_injective u lambda)
    (h.trans (quasiHillL2SolutionCurve_zero_initial u lambda).symm)
  have hs := congrArg Prod.snd he
  norm_num at hs

end NLS.MKdV
