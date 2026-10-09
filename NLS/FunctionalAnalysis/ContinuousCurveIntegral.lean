import NLS.FunctionalAnalysis.LinearVolterra
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Continuity of actual curve integrals in the uniform norm -/
noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace NLS.LinearVolterra

/-- The ordinary interval integral is continuous in the uniform curve norm. -/
theorem continuous_curve_intervalIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] (t : Icc (0:ℝ) 1) :
    Continuous (fun w : Curve E => ∫ s in (0:ℝ)..t.val, extend w s) := by
  let B : Curve E →L[ℝ] (ℝ →ᵇ E) :=
    (BoundedContinuousFunction.compContinuousCLM E ℝ
      ⟨projIcc 0 1 (by norm_num),continuous_projIcc⟩).comp
      (ContinuousMap.linearIsometryBoundedOfCompact (Icc (0:ℝ) 1) E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let L := (BoundedContinuousFunction.toLp 1 (volume.restrict (Ioc 0 t.val)) ℝ).comp B
  have h := MeasureTheory.continuous_integral.comp L.continuous
  convert h using 1
  ext w
  rw [intervalIntegral.integral_of_le t.property.1]
  apply integral_congr_ae
  exact (BoundedContinuousFunction.coeFn_toLp 1 (volume.restrict (Ioc 0 t.val)) ℝ (B w)).symm

/-- Uniform convergence passes the square integral of a real curve to the limit. -/
theorem continuous_curve_squareIntegral (t : Icc (0:ℝ) 1) :
    Continuous (fun w : Curve ℝ => ∫ s in (0:ℝ)..t.val, (extend w s)^2) := by
  have h := (continuous_curve_intervalIntegral (E := ℝ) t).comp
    (continuous_id.mul continuous_id : Continuous (fun w : Curve ℝ => w*w))
  simpa only [Function.comp_def,Pi.mul_apply,id_eq,NLS.LinearVolterra.extend,ContinuousMap.mul_apply,pow_two] using h

end NLS.LinearVolterra
