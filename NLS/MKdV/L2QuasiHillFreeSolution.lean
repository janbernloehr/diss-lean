import NLS.MKdV.L2QuasiHillDiscriminant
import NLS.MKdV.L2QuasiHillWeakEquation
import NLS.KdV.ClassicalHillFreeDirichlet

/-! # The actual free rough Hill IVP and kinetic form

Zero physical profile gives exactly the ordinary free Hill state with
its original position/derivative initial data, at every complex energy.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.KdV
namespace NLS.MKdV

theorem shiftedMiuraWeakForm_zero_profile (y φ : Curve ℂ) :
    shiftedMiuraWeakForm 0 0 y φ =
      ∫ s in (0 : ℝ)..1, deriv (extend y) s*deriv (extend φ) s := by
  simp only [shiftedMiuraWeakForm,zero_mul,sub_zero]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict (Ioc (0 : ℝ) 1))] with s hs
  simp only [Pi.zero_apply] at hs
  simp only [hs,zero_mul,sub_zero]

theorem continuousQuasiHillL2_zero : continuousQuasiHillL2 (0 : Curve ℂ) = 0 := by
  apply Lp.ext
  filter_upwards [continuousQuasiHillL2_representative (0 : Curve ℂ),
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict (Ioc (0 : ℝ) 1))] with s hs ht
  rw [hs,ht]
  rfl

theorem l2QuasiHillSolution_zero_profile (lambda : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    l2QuasiHillSolution 0 lambda v t = classicalHillFlow 0 lambda v t := by
  rw [← continuousQuasiHillL2_zero,l2QuasiHillSolution_continuous]
  have he : realCoefficient (quasiHillCoefficientCurve 0 lambda) = classicalHillCoefficientCurve 0 lambda := by
    apply ContinuousMap.ext
    intro s
    apply ContinuousLinearMap.ext
    intro w
    change (quasiHillCoefficientCurve 0 lambda s) w = classicalHillCoefficient 0 lambda w
    rw [quasiHillCoefficientCurve_apply]
    change quasiHillCoefficient 0 lambda w = classicalHillCoefficient 0 lambda w
    simp only [quasiHillCoefficient_apply,classicalHillCoefficient_apply,zero_mul,zero_add,sub_zero,zero_sub]
  change solution (realCoefficient (quasiHillCoefficientCurve 0 lambda)) v t = _
  rw [he]
  rfl

theorem l2QuasiHillPosition_zero_profile_sq (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    l2QuasiHillPosition 0 (z^2) (0,1) t = sin (z*t.val)/z := by
  change (l2QuasiHillSolution 0 (z^2) (0,1) t).1 = _
  rw [l2QuasiHillSolution_zero_profile,classicalHillFlow_free_sine z hz]

theorem l2QuasiHillMomentum_zero_profile_sq (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    l2QuasiHillMomentum 0 (z^2) (0,1) t = cos (z*t.val) := by
  change (l2QuasiHillSolution 0 (z^2) (0,1) t).2 = _
  rw [l2QuasiHillSolution_zero_profile,classicalHillFlow_free_sine z hz]

end NLS.MKdV
