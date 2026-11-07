import NLS.KdV.HillPeriodOneRestrictionInverse
import NLS.KdV.HillLocallyUniformActionTails
import NLS.SequenceSpaces.ConjugateDuality
import NLS.SequenceSpaces.Translation
import NLS.SequenceSpaces.Reflection
import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra
import NLS.Fourier.PeriodOneCoefficientLinear
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The quadratic KdV nonlinearity is well defined mode by mode on physical
L². Its convolution is absolutely convergent, with no multiplication of
L² functions asserted in L². Frequencies use the physical factor 2πn. -/
noncomputable section
set_option autoImplicit false
open Complex Filter Topology
namespace NLS.KdV

def kdvUnitFourierCLM : C(AddCircle (2 : ℝ),ℂ) →L[ℂ] Coeff 2 :=
  (Coeff.restrictIndicesCLM (Coeff.parityEmbedding 0)).comp Fourier.continuousFourierCLM

theorem kdvUnitFourierCLM_apply (Q : C(AddCircle (2 : ℝ),ℂ)) (n : ℤ) :
    kdvUnitFourierCLM Q n = fourierCoeff Q (2*n) := by
  change Fourier.continuousFourierCLM Q (2*n+0) = _
  simpa only [add_zero] using Fourier.continuousFourierCLM_apply Q (2*n)

/-- Absolute convergence follows from the L² coefficient pairing. -/
def kdvQuadraticMode (a : Coeff 2) (n : ℤ) : ℂ :=
  Coeff.dualPairing (Coeff.shift n (Coeff.reflection a)) a

theorem kdvQuadraticMode_eq_tsum (a : Coeff 2) (n : ℤ) :
    kdvQuadraticMode a n = ∑' j : ℤ, a (n-j)*a j := by
  simp only [kdvQuadraticMode,Coeff.dualPairing_apply,Coeff.shift_apply,Coeff.reflection_apply,
    neg_sub]

theorem summable_kdvQuadraticMode (a : Coeff 2) (n : ℤ) :
    Summable (fun j : ℤ => ‖a (n-j)*a j‖) := by
  simpa only [Coeff.shift_apply,Coeff.reflection_apply,neg_sub] using
    Coeff.summable_norm_dualPairing (Coeff.shift n (Coeff.reflection a)) a

theorem norm_kdvQuadraticMode_le (a : Coeff 2) (n : ℤ) :
    ‖kdvQuadraticMode a n‖ ≤ ‖a‖^2 := by
  simpa only [kdvQuadraticMode,Coeff.norm_shift,Coeff.reflection.norm_map,pow_two] using
    Coeff.norm_dualPairing_le (Coeff.shift n (Coeff.reflection a)) a

def kdvFourierModeField (a : Coeff 2) (n : ℤ) : ℂ :=
  -(2*I*(Real.pi:ℂ)*n)^3*a n+3*(2*I*(Real.pi:ℂ)*n)*kdvQuadraticMode a n

theorem continuous_kdvFourierModeField (n : ℤ) :
    Continuous (fun a : Coeff 2 => kdvFourierModeField a n) := by
  unfold kdvFourierModeField kdvQuadraticMode
  exact (continuous_const.mul (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous).add
    (continuous_const.mul ((Coeff.dualPairing.continuous.comp
      ((Coeff.shift n).continuous.comp Coeff.reflection.continuous)).clm_apply continuous_id))

/-- Integrated Fourier weak KdV in physical unit-period L² coefficients.
This definition is independent of spectral invariants and approximation. -/
def IsFourierWeakKdVCoefficients (a : ℝ → Coeff 2) : Prop :=
  Continuous a ∧ ∀ n : ℤ, ∀ s t : ℝ,
    a t n-a s n = ∫ τ in s..t, kdvFourierModeField (a τ) n

theorem isFourierWeakKdVCoefficients_iff (a : ℝ → Coeff 2) (ha : Continuous a) :
    IsFourierWeakKdVCoefficients a ↔
      ∀ (n : ℤ) (t : ℝ), HasDerivAt (fun τ => a τ n) (kdvFourierModeField (a t) n) t := by
  constructor
  · rintro ⟨_,h⟩ n t
    have hc := (continuous_kdvFourierModeField n).comp ha
    have hd := intervalIntegral.integral_hasDerivAt_right
      (hc.intervalIntegrable 0 t) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    have he : (fun r => a r n) = fun r => (∫ τ in (0:ℝ)..r, kdvFourierModeField (a τ) n)+a 0 n := by
      funext r
      linear_combination h n 0 r
    rw [he]
    exact hd.add_const _
  · intro h
    refine ⟨ha,fun n s t => ?_⟩
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => h n r)
      (((continuous_kdvFourierModeField n).comp ha).intervalIntegrable s t)).symm

end NLS.KdV
