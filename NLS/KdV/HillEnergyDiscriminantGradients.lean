import NLS.KdV.HillL2EnergyStateCurves
import NLS.KdV.HillDiscriminantGardnerCommutation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem trace_gradient_curve_polynomial (q : Coeff 2) (z : ℂ) :
    hillDiscriminantGradientCurve q z=
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1 •
        ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillL2FrequencyStateCurve q z (1,0)))^2+
      ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1) •
        (((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillL2FrequencyStateCurve q z (1,0)))*
          ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillL2FrequencyStateCurve q z (0,1))))-
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2 •
        ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillL2FrequencyStateCurve q z (0,1)))^2 := by
  ext t
  change hillDiscriminantGradientCurve q z t=
    (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1*(hillL2FrequencyStateCurve q z (1,0) t).1^2+
    ((hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2-
      (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).1)*
      ((hillL2FrequencyStateCurve q z (1,0) t).1*(hillL2FrequencyStateCurve q z (0,1) t).1)-
    (hillL2FrequencyStateCurve q z (1,0) ⟨1,by norm_num⟩).2*(hillL2FrequencyStateCurve q z (0,1) t).1^2
  simpa only [mul_assoc] using hillDiscriminantGradientCurve_eq_scalar_polynomial q z t

theorem continuous_hillDiscriminantGradientCurve_joint :
    Continuous (fun p : ℂ × Coeff 2 => hillDiscriminantGradientCurve p.2 p.1) := by
  have hC := continuous_hillL2FrequencyStateCurve_joint (1,0)
  have hS := continuous_hillL2FrequencyStateCurve_joint (0,1)
  have hc := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hC
  have hs := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hS
  have hC1 := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hC
  have hS1 := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hS
  have he := funext (fun p : ℂ × Coeff 2 => trace_gradient_curve_polynomial p.2 p.1)
  rw [he]
  exact ((hS1.fst.smul (hc.pow 2)).add ((hS1.snd.sub hC1.fst).smul (hc.mul hs))).sub
    (hC1.snd.smul (hs.pow 2))

theorem continuous_hillDiscriminantGradientSpatialCurve_joint :
    Continuous (fun p : ℂ × Coeff 2 => hillDiscriminantGradientSpatialCurve p.2 p.1) := by
  have hC := continuous_hillL2FrequencyStateCurve_joint (1,0)
  have hS := continuous_hillL2FrequencyStateCurve_joint (0,1)
  have hc := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hC
  have hd := (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hC
  have hs := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hS
  have ht := (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hS
  have hC1 := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hC
  have hS1 := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hS
  exact (((hS1.fst.const_mul 2).smul (hc.mul hd)).add
    ((hS1.snd.sub hC1.fst).smul ((hd.mul hs).add (hc.mul ht)))).sub
      ((hC1.snd.const_mul 2).smul (hs.mul ht))

theorem hillDiscriminantGradientCurve_even (q : Coeff 2) (z : ℂ) :
    hillDiscriminantGradientCurve q (-z)=hillDiscriminantGradientCurve q z := by
  rw [trace_gradient_curve_polynomial,trace_gradient_curve_polynomial]
  rw [hillL2FrequencyStateCurve_even,hillL2FrequencyStateCurve_even]

theorem hillDiscriminantGradientSpatialCurve_even (q : Coeff 2) (z : ℂ) :
    hillDiscriminantGradientSpatialCurve q (-z)=hillDiscriminantGradientSpatialCurve q z := by
  simp only [hillDiscriminantGradientSpatialCurve,hillL2FrequencyStateCurve_even]

def hillEnergyDiscriminantGradientCurve (q : Coeff 2) (energy : ℂ) : Curve ℂ :=
  hillDiscriminantGradientCurve q (Complex.sqrt energy)

def hillEnergyDiscriminantGradientSpatialCurve (q : Coeff 2) (energy : ℂ) : Curve ℂ :=
  hillDiscriminantGradientSpatialCurve q (Complex.sqrt energy)

theorem continuous_hillEnergyDiscriminantGradientCurve_joint :
    Continuous (fun p : ℂ × Coeff 2 => hillEnergyDiscriminantGradientCurve p.2 p.1) :=
  continuous_even_square_descent (fun p : ℂ × Coeff 2 => hillDiscriminantGradientCurve p.2 p.1)
    continuous_hillDiscriminantGradientCurve_joint hillDiscriminantGradientCurve_even Complex.sqrt complex_sqrt_sq

theorem continuous_hillEnergyDiscriminantGradientSpatialCurve_joint :
    Continuous (fun p : ℂ × Coeff 2 => hillEnergyDiscriminantGradientSpatialCurve p.2 p.1) :=
  continuous_even_square_descent (fun p : ℂ × Coeff 2 => hillDiscriminantGradientSpatialCurve p.2 p.1)
    continuous_hillDiscriminantGradientSpatialCurve_joint hillDiscriminantGradientSpatialCurve_even Complex.sqrt complex_sqrt_sq

/-- The energy cotangent represents the actual energy discriminant
variation, with the original constant-upper Hill normalization. -/
theorem hillEnergyDiscriminantGradient_represents_potential (q h : Coeff 2) (energy : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p energy) q) h=
      hillPhysicalDirectionPairing h (hillEnergyDiscriminantGradientCurve q energy) :=
  hillDiscriminantGradient_represents_potential q h (Complex.sqrt energy)

theorem hillEnergyDiscriminantGradient_H1 (q : Coeff 2) (energy : ℂ) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve q energy)) 0 1 ∧
      MemLp (NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve q energy)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      MemLp (deriv (NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve q energy))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  hillDiscriminantGradient_H1 q (Complex.sqrt energy)

theorem ae_hasDerivAt_hillEnergyDiscriminantGradientCurve (q : Coeff 2) (energy : ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve q energy))
        (NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientSpatialCurve q energy) x) x :=
  ae_hasDerivAt_hillDiscriminantGradientCurve q (Complex.sqrt energy)

theorem hillEnergyDiscriminantGardnerBracket_eq_zero (q : Coeff 2) (energy μ : ℂ) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve q energy) x*
      deriv (NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve q μ)) x)=0 :=
  hillDiscriminantGardnerBracket_eq_zero q (Complex.sqrt energy) (Complex.sqrt μ)

end NLS.KdV
