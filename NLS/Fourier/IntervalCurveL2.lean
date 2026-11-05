import NLS.Fourier.IntervalL2Products

/-! # Joint bounded multiplication of continuous curves and physical L2 classes -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.Fourier

def intervalCurveL2 : Curve ℂ →L[ℂ] IntervalL2 :=
  (BoundedContinuousFunction.toLp 2 (volume.restrict (Ioc (0 : ℝ) 1)) ℂ).comp
    (curveBoundedExtension ℂ)

theorem intervalCurveL2_representative (f : Curve ℂ) :
    intervalCurveL2 f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] extend f :=
  BoundedContinuousFunction.coeFn_toLp 2 (volume.restrict (Ioc (0 : ℝ) 1)) ℂ (curveBoundedExtension ℂ f)

theorem intervalCurveMulCLM_add (f g : Curve ℂ) :
    intervalCurveMulCLM (f+g) = intervalCurveMulCLM f+intervalCurveMulCLM g := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [intervalCurveMul_representative (f+g) u,
    intervalCurveMul_representative f u,intervalCurveMul_representative g u,
    Lp.coeFn_add (intervalCurveMul f u) (intervalCurveMul g u)] with s h h₁ h₂ ha
  simp only [add_apply,intervalCurveMulCLM_apply] at *
  rw [h,ha]
  simp only [Pi.add_apply,NLS.LinearVolterra.extend,ContinuousMap.add_apply] at *
  rw [h₁,h₂,mul_add]

theorem intervalCurveMulCLM_smul (c : ℂ) (f : Curve ℂ) :
    intervalCurveMulCLM (c • f) = c • intervalCurveMulCLM f := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [intervalCurveMul_representative (c • f) u,
    intervalCurveMul_representative f u,Lp.coeFn_smul c (intervalCurveMul f u)] with s h h₁ hs
  simp only [smul_apply,intervalCurveMulCLM_apply] at *
  rw [h,hs]
  simp only [Pi.smul_apply,smul_eq_mul,NLS.LinearVolterra.extend,ContinuousMap.smul_apply] at *
  rw [h₁]
  ring

theorem norm_intervalCurveMulCLM_le (f : Curve ℂ) : ‖intervalCurveMulCLM f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact norm_intervalCurveMul_le f

def intervalCurveMultiplication : Curve ℂ →L[ℂ] IntervalL2 →L[ℂ] IntervalL2 :=
  LinearMap.mkContinuous
    { toFun := intervalCurveMulCLM
      map_add' := intervalCurveMulCLM_add
      map_smul' := fun c f => by simpa only [RingHom.id_apply] using intervalCurveMulCLM_smul c f }
    1 (by intro f; simpa only [one_mul] using! norm_intervalCurveMulCLM_le f)

@[simp] theorem intervalCurveMultiplication_apply (f : Curve ℂ) (u : IntervalL2) :
    intervalCurveMultiplication f u = intervalCurveMul f u := rfl

theorem intervalCurveL2_mul (f g : Curve ℂ) :
    intervalCurveL2 (f*g) = intervalCurveMultiplication f (intervalCurveL2 g) := by
  apply Lp.ext
  filter_upwards [intervalCurveL2_representative (f*g),intervalCurveL2_representative g,
    intervalCurveMul_representative f (intervalCurveL2 g)] with s h h₁ h₂
  rw [intervalCurveMultiplication_apply,h,h₂,h₁]
  change extend f s*extend g s = extend g s*extend f s
  ring

end NLS.Fourier
