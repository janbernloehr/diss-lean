import NLS.Fourier.PeriodOneCoefficients
import NLS.ComplexAnalysis.CosineFourierIntegral
import NLS.Fourier.SobolevSynthesis

/-! # The bounded continuous mean and its physical unit-period normalization -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Fourier

def continuousCircleMean : C(AddCircle (2 : ℝ), ℂ) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).comp continuousFourierCLM

theorem continuousCircleMean_eq_periodOne_integral
    (f : C(AddCircle (2 : ℝ), ℂ))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    continuousCircleMean f = ∫ x in (0 : ℝ)..1, f (x : AddCircle (2 : ℝ)) := by
  change continuousFourierCLM f 0 = _
  rw [continuousFourierCLM_apply,←periodTwoCoefficient_circle]
  rw [show (0 : ℤ)=2*0 by norm_num,periodTwoCoefficient_periodic_even _ hp
    ((f.continuous.comp (by fun_prop)).intervalIntegrable 0 1)]
  exact (NLS.ComplexAnalysis.integral_eq_periodOneCoefficient_zero _).symm

end NLS.Fourier
