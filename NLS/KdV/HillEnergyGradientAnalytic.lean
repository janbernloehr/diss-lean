import NLS.KdV.HillEnergyStateAnalytic
import NLS.KdV.HillEnergyDiscriminantGradients

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem energy_gradient_polynomial (p : Coeff 2) (E : ℂ) :
    hillEnergyDiscriminantGradientCurve p E=
      (hillL2EnergyStateCurve p E (0,1) ⟨1,by norm_num⟩).1 •
        ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillL2EnergyStateCurve p E (1,0)))^2+
      ((hillL2EnergyStateCurve p E (0,1) ⟨1,by norm_num⟩).2-
        (hillL2EnergyStateCurve p E (1,0) ⟨1,by norm_num⟩).1) •
        (((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillL2EnergyStateCurve p E (1,0)))*
          ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillL2EnergyStateCurve p E (0,1))))-
      (hillL2EnergyStateCurve p E (1,0) ⟨1,by norm_num⟩).2 •
        ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillL2EnergyStateCurve p E (0,1)))^2 := by
  ext t
  change hillDiscriminantGradientCurve p (Complex.sqrt E) t=
    (hillL2FrequencyStateCurve p (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).1*(hillL2FrequencyStateCurve p (Complex.sqrt E) (1,0) t).1^2+
    ((hillL2FrequencyStateCurve p (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
      (hillL2FrequencyStateCurve p (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1)*
      ((hillL2FrequencyStateCurve p (Complex.sqrt E) (1,0) t).1*(hillL2FrequencyStateCurve p (Complex.sqrt E) (0,1) t).1)-
    (hillL2FrequencyStateCurve p (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2*(hillL2FrequencyStateCurve p (Complex.sqrt E) (0,1) t).1^2
  simpa only [mul_assoc] using hillDiscriminantGradientCurve_eq_scalar_polynomial p (Complex.sqrt E) t

/-- The actual energy discriminant cotangent is entire in the uniform physical curve norm. -/
theorem analyticOnNhd_hillEnergyDiscriminantGradientCurve_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillEnergyDiscriminantGradientCurve p.2 p.1) univ := by
  intro p _
  have hC := analyticOnNhd_hillL2EnergyStateCurve_joint (1,0) p (mem_univ _)
  have hS := analyticOnNhd_hillL2EnergyStateCurve_joint (0,1) p (mem_univ _)
  let F := (ContinuousLinearMap.fst ℂ ℂ ℂ).compLeftContinuous ℂ (Icc (0 : ℝ) 1)
  have hc := (F.analyticAt _).comp hC
  have hs := (F.analyticAt _).comp hS
  have hC1 := ((ContinuousMap.evalCLM ℂ (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).analyticAt _).comp hC
  have hS1 := ((ContinuousMap.evalCLM ℂ (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).analyticAt _).comp hS
  have hG := (((analyticAt_fst.comp hS1).smul (hc.pow 2)).add (((analyticAt_snd.comp hS1).sub (analyticAt_fst.comp hC1)).smul (hc.mul hs))).sub
    ((analyticAt_snd.comp hC1).smul (hs.pow 2))
  apply hG.congr
  exact Eventually.of_forall (fun r => (energy_gradient_polynomial r.2 r.1).symm)

/-- The actual spatial energy-discriminant cotangent is entire as a physical curve,
including spectral energy zero. -/
theorem analyticOnNhd_hillEnergyDiscriminantGradientSpatialCurve_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillEnergyDiscriminantGradientSpatialCurve p.2 p.1) univ := by
  intro p _
  have hC := analyticOnNhd_hillL2EnergyStateCurve_joint (1,0) p (mem_univ _)
  have hS := analyticOnNhd_hillL2EnergyStateCurve_joint (0,1) p (mem_univ _)
  let F := (ContinuousLinearMap.fst ℂ ℂ ℂ).compLeftContinuous ℂ (Icc (0 : ℝ) 1)
  let G := (ContinuousLinearMap.snd ℂ ℂ ℂ).compLeftContinuous ℂ (Icc (0 : ℝ) 1)
  have hc := (F.analyticAt _).comp hC
  have hd := (G.analyticAt _).comp hC
  have hs := (F.analyticAt _).comp hS
  have ht := (G.analyticAt _).comp hS
  have hC1 := ((ContinuousMap.evalCLM ℂ (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).analyticAt _).comp hC
  have hS1 := ((ContinuousMap.evalCLM ℂ (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).analyticAt _).comp hS
  exact ((((analyticAt_const (v := (2 : ℂ))).mul (analyticAt_fst.comp hS1)).smul (hc.mul hd)).add
    (((analyticAt_snd.comp hS1).sub (analyticAt_fst.comp hC1)).smul ((hd.mul hs).add (hc.mul ht)))).sub
      (((analyticAt_const (v := (2 : ℂ))).mul (analyticAt_snd.comp hC1)).smul (hs.mul ht))

end NLS.KdV
