import NLS.ZakharovShabat.PhysicalL2Primitive
import NLS.ComplexAnalysis.OscillatoryIntegralParts
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Actual oscillatory primitives as uniform L2 maps

Factor the oscillatory kernel into a fixed weighted primitive and a free
exponential. This gives uniform convergence in time under L2 approximation.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped BoundedContinuousFunction
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The continuous exponential on the physical interval. -/
def intervalExponential (c : ℂ) : Curve ℂ := ⟨fun t => exp (c*t.val),by fun_prop⟩

/-- The actual oscillatory primitive, as a bounded complex-linear map into continuous curves. -/
def l2OscillatoryCurve (c : ℂ) : IntervalL2 →L[ℂ] Curve ℂ :=
  (ContinuousLinearMap.mul ℂ (Curve ℂ) (intervalExponential c)).comp
    (intervalL2PrimitiveCLM (curveBoundedExtension ℂ (intervalExponential (-2*c))))

/-- Evaluation is exactly the original oscillatory integral of the L2 representative. -/
theorem l2OscillatoryCurve_apply (c : ℂ) (u : IntervalL2) (t : Icc (0:ℝ) 1) :
    l2OscillatoryCurve c u t = oscillatoryIntegral c t u := by
  change exp (c*t.val)*(∫ s in (0:ℝ)..t.val,
    u s*curveBoundedExtension ℂ (intervalExponential (-2*c)) s) = _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le t.property.1] at hs
    exact ⟨hs.1,hs.2.trans t.property.2⟩
  simp only [curveBoundedExtension_apply,NLS.LinearVolterra.extend,projIcc_of_mem _ hs',
    intervalExponential,ContinuousMap.coe_mk,oscillatoryKernel]
  rw [mul_comm (u s) _,← mul_assoc,← exp_add]
  congr 2
  push_cast
  ring

/-- Exact recovery for an original L2 function, independently of null-set changes. -/
theorem l2OscillatoryCurve_apply_ofFunction (c : ℂ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (t : Icc (0:ℝ) 1) :
    l2OscillatoryCurve c (hf.toLp f) t = oscillatoryIntegral c t f := by
  rw [l2OscillatoryCurve_apply]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le t.property.1]
  filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
    hf.coeFn_toLp] with s hs
  rw [hs]

end NLS.ZakharovShabat
