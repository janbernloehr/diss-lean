import NLS.ZakharovShabat.ClassicalScalarForcingFreeComparison

/-! # The actual lower scalar forcing kernel

The lower component of the scalar forced solution equals its integral against the actual fundamental-matrix propagator.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The lower-to-lower entry of the actual propagator, expressed through
its normalized fundamental columns. -/
def classicalScalarForcingLowerKernel (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t x : ℝ) : ℂ :=
  (classicalSolution Φ z (1,0) x).1*(classicalSolution Φ z (0,1) t).2-
    (classicalSolution Φ z (0,1) x).1*(classicalSolution Φ z (1,0) t).2

theorem continuous_classicalScalarForcingLowerKernel
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    Continuous (classicalScalarForcingLowerKernel Φ z t) := by
  exact ((continuous_classicalSolution Φ z (1,0)).fst.mul continuous_const).sub
    ((continuous_classicalSolution Φ z (0,1)).fst.mul continuous_const)

/-- The actual second component for a scalar lower forcing is its exact
propagator integral over the partial physical interval. -/
theorem classicalScalarForcing_snd_eq_lowerKernel_integral
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (f : ℝ → ℂ) (hf : Continuous f)
    (t : Icc (0:ℝ) 1) :
    (classicalForcedKernelSolution Φ (classicalScalarForcing f hf) z t).2 =
      ∫ x in (0:ℝ)..t.val, classicalScalarForcingLowerKernel Φ z t x*f x := by
  let g := classicalScalarForcing f hf
  have hc := continuous_classicalForcedKernelIntegrand Φ g z
  have hfst : (classicalForcedKernelPrimitive Φ g z t).1 =
      ∫ x in (0:ℝ)..t.val, (classicalForcedKernelIntegrand Φ g z x).1 :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).intervalIntegral_comp_comm (hc.intervalIntegrable _ _)).symm
  have hsnd : (classicalForcedKernelPrimitive Φ g z t).2 =
      ∫ x in (0:ℝ)..t.val, (classicalForcedKernelIntegrand Φ g z x).2 :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).intervalIntegral_comp_comm (hc.intervalIntegrable _ _)).symm
  change (classicalForcedKernelSolution Φ g z t).2 = _
  simp only [classicalForcedKernelSolution,Prod.snd_add,Prod.smul_snd,smul_eq_mul]
  have h₁ : IntervalIntegrable (fun x => (classicalForcedKernelIntegrand Φ g z x).1*
      (classicalSolution Φ z (1,0) t).2) volume 0 t.val :=
    (hc.fst.mul continuous_const).intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun x => (classicalForcedKernelIntegrand Φ g z x).2*
      (classicalSolution Φ z (0,1) t).2) volume 0 t.val :=
    (hc.snd.mul continuous_const).intervalIntegrable _ _
  rw [hfst,hsnd,← intervalIntegral.integral_mul_const,← intervalIntegral.integral_mul_const,
    ← intervalIntegral.integral_add h₁ h₂]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le t.property.1] at hx
  let u : Icc (0:ℝ) 1 := ⟨x,hx.1,hx.2.trans t.property.2⟩
  change (classicalForcedKernelIntegrand Φ g z u).1*(classicalSolution Φ z (1,0) t).2+
    (classicalForcedKernelIntegrand Φ g z u).2*(classicalSolution Φ z (0,1) t).2 = _
  simp only [classicalForcedKernelIntegrand,extend_coe,g,classicalScalarForcing,
    ContinuousMap.coe_mk,classicalScalarForcingLowerKernel,mul_zero,zero_sub,zero_add]
  ring

end NLS.ZakharovShabat
