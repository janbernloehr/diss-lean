import NLS.MKdV.QuasiHillL2PhysicalSource
import NLS.ZakharovShabat.L2SolutionDifferentialEquation
import NLS.ZakharovShabat.L2WholeLinePeriodAbsoluteContinuity
import NLS.ZakharovShabat.L2InitialValueACUniqueness

/-! The actual rough quasi-Hill solution is absolutely continuous and
solves its scalar first-order equations almost everywhere. Conversely every
absolutely continuous weak solution is that IVP solution. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
open NLS.Fourier NLS.ZakharovShabat
namespace NLS.MKdV

/-- Inverse of the fixed energy state map, as a bounded complex-linear map. -/
def quasiHillEnergyInverseStateMap : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (((1/2:ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ)-((I/2) • ContinuousLinearMap.snd ℂ ℂ ℂ)).prod
    (((1/2:ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ)+((I/2) • ContinuousLinearMap.snd ℂ ℂ ℂ))

theorem quasiHillEnergyInverseStateMap_apply (v : ℂ × ℂ) :
    quasiHillEnergyInverseStateMap v = quasiHillEnergyInitialVector v := by
  apply Prod.ext
  · change (1/2:ℂ)*v.1-(I/2)*v.2 = (v.1-I*v.2)/2
    ring
  · change (1/2:ℂ)*v.1+(I/2)*v.2 = (v.1+I*v.2)/2
    ring

theorem quasiHillEnergyInitialVector_stateMap (v : ℂ × ℂ) :
    quasiHillEnergyInitialVector (quasiHillEnergyStateMap v) = v := by
  apply Prod.ext <;> simp only [quasiHillEnergyInitialVector,quasiHillEnergyStateMap_apply]
  all_goals ring_nf
  all_goals simp [I_sq]
  all_goals ring

/-- The inverse gauge carries the scalar equation to the actual first-order equation. -/
theorem quasiHillEnergyInverseStateMap_ode (u lambda : ℂ) (v : ℂ × ℂ) :
    quasiHillEnergyInverseStateMap (quasiHillCoefficient u lambda v) =
      classicalODECoefficient (-I*u+(lambda-1)/2,I*u+(lambda-1)/2) (-(lambda+1)/2)
        (quasiHillEnergyInverseStateMap v) := by
  rw [quasiHillEnergyInverseStateMap_apply,quasiHillEnergyInverseStateMap_apply]
  have h := congrArg quasiHillEnergyInitialVector
    (quasiHillEnergyStateMap_ode u lambda (quasiHillEnergyInitialVector v))
  rw [quasiHillEnergyStateMap_initialVector,quasiHillEnergyInitialVector_stateMap] at h
  exact h

/-- The full scalar state is absolutely continuous on the closed unit interval. -/
theorem absolutelyContinuousOnInterval_quasiHillL2SolutionCurve
    (u : Coeff 2) (lambda : ℂ) (v : ℂ × ℂ) :
    AbsolutelyContinuousOnInterval (extend (quasiHillL2SolutionCurve u lambda v)) 0 1 := by
  exact absolutelyContinuousOnInterval_clm
    (absolutelyContinuousOnInterval_l2SolutionCurve
      (sourcePhysicalL2 (quasiHillEnergySource u lambda)) (-(lambda+1)/2)
      (quasiHillEnergyInitialVector v)) (quasiHillEnergyStateMap.restrictScalars ℝ)

/-- The constructed state solves the literal scalar quasi-derivative ODE
for the original L2 representative, with no smoothness premise. -/
theorem ae_hasDerivAt_quasiHillL2SolutionCurve (u : Coeff 2) (lambda : ℂ) (v : ℂ × ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt
      (extend (quasiHillL2SolutionCurve u lambda v))
      (quasiHillCoefficient (unitL2SynthesisEquiv u x) lambda
        (extend (quasiHillL2SolutionCurve u lambda v) x)) x := by
  filter_upwards [ae_hasDerivAt_l2SolutionCurve
    (sourcePhysicalL2 (quasiHillEnergySource u lambda)) (-(lambda+1)/2) (quasiHillEnergyInitialVector v),
    quasiHillEnergySource_representative u lambda] with x hx hphi
  have h := ((quasiHillEnergyStateMap.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt x hx
  change HasDerivAt (fun y => quasiHillEnergyStateMap (extend (l2SolutionCurve _ _ _) y))
    (quasiHillEnergyStateMap (classicalODECoefficient
      (intervalL2Representative (sourcePhysicalL2 (quasiHillEnergySource u lambda)) x)
      (-(lambda+1)/2) (extend (l2SolutionCurve _ _ _) x))) x at h
  rw [hphi,← quasiHillEnergyStateMap_ode] at h
  exact h

/-- Any absolutely continuous state satisfying the same physical weak ODE
is the constructed solution with its own initial position/quasi-derivative. -/
theorem quasiHillL2SolutionCurve_unique_of_ac (u : Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ))
    (hw : AbsolutelyContinuousOnInterval (extend w) 0 1)
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt (extend w)
      (quasiHillCoefficient (unitL2SynthesisEquiv u x) lambda (extend w x)) x) :
    w = quasiHillL2SolutionCurve u lambda (w ⟨0,by constructor <;> norm_num⟩) := by
  let W := ContinuousLinearMap.compLeftContinuous ℂ (Icc (0:ℝ) 1) quasiHillEnergyInverseStateMap w
  have hW : AbsolutelyContinuousOnInterval (extend W) 0 1 :=
    absolutelyContinuousOnInterval_clm hw (quasiHillEnergyInverseStateMap.restrictScalars ℝ)
  have hdW : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt (extend W)
      (classicalODECoefficient
        (intervalL2Representative (sourcePhysicalL2 (quasiHillEnergySource u lambda)) x)
        (-(lambda+1)/2) (extend W x)) x := by
    filter_upwards [hd,quasiHillEnergySource_representative u lambda] with x hx hphi
    have h := ((quasiHillEnergyInverseStateMap.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt x hx
    change HasDerivAt (fun y => quasiHillEnergyInverseStateMap (extend w y))
      (quasiHillEnergyInverseStateMap (quasiHillCoefficient (unitL2SynthesisEquiv u x) lambda (extend w x))) x at h
    rw [quasiHillEnergyInverseStateMap_ode] at h
    rw [hphi]
    exact h
  have he := l2SolutionCurve_unique_of_ac (sourcePhysicalL2 (quasiHillEnergySource u lambda))
    (-(lambda+1)/2) W hW hdW
  apply ContinuousMap.ext
  intro t
  have h := congrArg (fun F : Curve (ℂ × ℂ) => quasiHillEnergyStateMap (F t)) he
  change quasiHillEnergyStateMap (quasiHillEnergyInverseStateMap (w t)) =
    quasiHillEnergyStateMap (l2SolutionCurve _ _
      (quasiHillEnergyInverseStateMap (w ⟨0,by constructor <;> norm_num⟩)) t) at h
  simp only [quasiHillEnergyInverseStateMap_apply,quasiHillEnergyStateMap_initialVector] at h
  exact h

end NLS.MKdV
