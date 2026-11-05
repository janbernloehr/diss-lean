import NLS.MKdV.L2QuasiHillPotential
import NLS.ZakharovShabat.L2SolutionDifferentialEquation
import NLS.FunctionalAnalysis.IntegralAbsoluteContinuity

/-! # The actual rough quasi-derivative Hill initial-value solution

The fixed invertible state map transports the existing physical L2
Volterra solver. The resulting curve has the prescribed initial data,
solves the representative-based quasi-derivative integral equation, is
absolutely continuous, and satisfies the differential equation almost
everywhere, at every complex energy including zero.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.FunctionalAnalysis
namespace NLS.MKdV

def quasiHillFixedCurve : Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1) quasiHillFixedState

def l2QuasiHillSolution (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  quasiHillFixedCurve (l2SolutionCurve (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ)
    (quasiHillFixedStateInv v))

@[simp] theorem l2QuasiHillSolution_apply (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    l2QuasiHillSolution u μ v t = quasiHillFixedState
      (l2SolutionCurve (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ) (quasiHillFixedStateInv v) t) := rfl

@[simp] theorem l2QuasiHillSolution_zero (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) :
    l2QuasiHillSolution u μ v ⟨0,by constructor <;> norm_num⟩ = v := by
  rw [l2QuasiHillSolution_apply,l2SolutionCurve_zero,quasiHillFixedState_right_inv]

theorem analyticOnNhd_l2QuasiHillSolution_joint (v : ℂ × ℂ) :
    AnalyticOnNhd ℂ (fun p : ℂ × IntervalL2 => l2QuasiHillSolution p.2 p.1 v) univ := by
  intro p _
  have hμ : AnalyticAt ℂ (fun p : ℂ × IntervalL2 => quasiHillAffineFrequency p.1) p :=
    (analyticAt_fst.add analyticAt_const).div_const
  have hpar : AnalyticAt ℂ (fun p : ℂ × IntervalL2 =>
      (quasiHillAffineFrequency p.1,l2QuasiHillPotential p.2 p.1)) p :=
    hμ.prod (analyticOnNhd_l2QuasiHillPotential_joint p (mem_univ p))
  have hsol : AnalyticAt ℂ (fun p : ℂ × IntervalL2 =>
      l2SolutionCurve (l2QuasiHillPotential p.2 p.1) (quasiHillAffineFrequency p.1) (quasiHillFixedStateInv v)) p :=
    (analyticOnNhd_l2SolutionCurve_joint (quasiHillFixedStateInv v) _ (mem_univ _)).comp
      (f := fun p : ℂ × IntervalL2 => (quasiHillAffineFrequency p.1,l2QuasiHillPotential p.2 p.1)) hpar
  exact (quasiHillFixedCurve.analyticAt _).comp
    (f := fun p : ℂ × IntervalL2 =>
      l2SolutionCurve (l2QuasiHillPotential p.2 p.1) (quasiHillAffineFrequency p.1) (quasiHillFixedStateInv v)) hsol

theorem l2QuasiHillSolution_eq_integral (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    l2QuasiHillSolution u μ v t = v+∫ s in (0 : ℝ)..t.val,
      quasiHillCoefficient (u s) μ (extend (l2QuasiHillSolution u μ v) s) := by
  let w := l2SolutionCurve (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ) (quasiHillFixedStateInv v)
  have hi := intervalIntegrable_l2ODECoefficient (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ) w t
  have he := congrArg quasiHillFixedState
    (l2SolutionCurve_eq_integral (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ) (quasiHillFixedStateInv v) t)
  rw [map_add,quasiHillFixedState_right_inv,← quasiHillFixedState.intervalIntegral_comp_comm hi] at he
  rw [l2QuasiHillSolution_apply,he]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le t.property.1]
  filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
    (l2QuasiHillPotential_representative u μ)] with s hs
  rw [hs,← quasiHillCoefficient_affine_intertwine]
  rfl

theorem intervalIntegrable_l2QuasiHillSolution_coefficient
    (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => quasiHillCoefficient (u s) μ
      (extend (l2QuasiHillSolution u μ v) s)) volume 0 t.val := by
  have ho := intervalIntegrable_l2ODECoefficient (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ)
    (l2SolutionCurve (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ) (quasiHillFixedStateInv v)) t
  have hi := And.intro (quasiHillFixedState.integrable_comp ho.1) (quasiHillFixedState.integrable_comp ho.2)
  apply IntervalIntegrable.congr_ae hi
  rw [uIoc_of_le t.property.1]
  filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
    (l2QuasiHillPotential_representative u μ)] with s hs
  rw [hs,← quasiHillCoefficient_affine_intertwine]
  rfl

theorem absolutelyContinuousOnInterval_l2QuasiHillSolution (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) :
    AbsolutelyContinuousOnInterval (extend (l2QuasiHillSolution u μ v)) 0 1 := by
  have hi := intervalIntegrable_l2QuasiHillSolution_coefficient u μ v ⟨1,by constructor <;> norm_num⟩
  have ha := absolutelyContinuousOnInterval_const_add
    (absolutelyContinuousOnInterval_integral hi (by simp : (0 : ℝ) ∈ uIcc 0 1)) v
  apply absolutelyContinuousOnInterval_congr ha
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ ht'] using
    (l2QuasiHillSolution_eq_integral u μ v ⟨t,ht'⟩).symm

theorem ae_hasDerivAt_l2QuasiHillSolution (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) :
    ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (l2QuasiHillSolution u μ v))
        (quasiHillCoefficient (u s) μ (extend (l2QuasiHillSolution u μ v) s)) s := by
  filter_upwards [ae_hasDerivAt_l2SolutionCurve (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ)
      (quasiHillFixedStateInv v),l2QuasiHillPotential_representative u μ] with s hs hu
  let w := l2SolutionCurve (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ) (quasiHillFixedStateInv v)
  have hd : HasDerivAt (fun x => quasiHillFixedState (extend w x))
      (quasiHillFixedState (classicalODECoefficient (intervalL2Representative (l2QuasiHillPotential u μ) s)
        (quasiHillAffineFrequency μ) (extend w s))) s :=
    (quasiHillFixedState.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hs
  rw [hu,← quasiHillCoefficient_affine_intertwine] at hd
  exact hd

end NLS.MKdV
