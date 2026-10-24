import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Variation of constants for scalar locally absolutely continuous solutions -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Complex
namespace NLS.FunctionalAnalysis

/-- The real-time complex exponential is smooth. -/
theorem contDiff_scalarExponential (α : ℂ) :
    ContDiff ℝ 1 (fun t : ℝ => Complex.exp (α*(t : ℂ))) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-- The derivative of the real-time complex exponential. -/
theorem hasDerivAt_scalarExponential (α : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (α*(s : ℂ)))
      (α*Complex.exp (α*(t : ℂ))) t := by
  simpa only [Function.comp_def,Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one,
    smul_eq_mul,mul_comm] using!
    (Complex.hasDerivAt_exp (α*(t : ℂ))).scomp t
      (Complex.ofRealCLM.hasDerivAt.const_mul α)

/-- An integrating factor converts the scalar equation into an exact integral identity. -/
theorem scalarAC_integratingFactor (α : ℂ) (y h : ℝ → ℂ) (a b : ℝ)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hh : IntervalIntegrable h volume a b)
    (hd : ∀ᵐ t : ℝ, t ∈ uIcc a b → HasDerivAt y (α*y t+h t) t) :
    (∫ t in a..b, Complex.exp (-α*(t : ℂ))*h t) =
      Complex.exp (-α*(b : ℂ))*y b-Complex.exp (-α*(a : ℂ))*y a := by
  have he := (contDiff_scalarExponential (-α)).contDiffOn.absolutelyContinuousOnInterval
    (a := a) (b := b)
  apply integral_eq_sub_of_ac_of_ae_hasDerivAt (he.smul hy)
    (hh.continuousOn_mul he.continuousOn)
  filter_upwards [hd] with t ht
  intro hab
  convert! (hasDerivAt_scalarExponential (-α) t).mul (ht hab) using 1
  ring

/-- Variation of constants, with the exponential depending only on elapsed time. -/
theorem scalarAC_variation (α : ℂ) (y h : ℝ → ℂ) (a b : ℝ)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hh : IntervalIntegrable h volume a b)
    (hd : ∀ᵐ t : ℝ, t ∈ uIcc a b → HasDerivAt y (α*y t+h t) t) :
    y b = Complex.exp (α*((b-a : ℝ) : ℂ))*y a+
      ∫ t in a..b, Complex.exp (α*((b-t : ℝ) : ℂ))*h t := by
  have hexp (t : ℝ) : Complex.exp (α*((b-t : ℝ) : ℂ)) =
      Complex.exp (α*(b : ℂ))*Complex.exp (-α*(t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hexp,mul_assoc]
  rw [intervalIntegral.integral_const_mul,scalarAC_integratingFactor α y h a b hy hh hd]
  have he : Complex.exp (α*(b : ℂ))*Complex.exp (-α*(b : ℂ)) = 1 := by
    rw [← Complex.exp_add,neg_mul,add_neg_cancel,Complex.exp_zero]
  linear_combination -y b*he

/-- A homogeneous locally AC solution is the original exponential mode on the interval. -/
theorem scalarAC_homogeneous (α : ℂ) (y : ℝ → ℂ) (a b : ℝ)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hd : ∀ᵐ t : ℝ, t ∈ uIcc a b → HasDerivAt y (α*y t) t) :
    y b = Complex.exp (α*((b-a : ℝ) : ℂ))*y a := by
  have hder : ∀ᵐ t : ℝ, t ∈ uIcc a b → HasDerivAt y (α*y t+0) t := by
    simpa only [add_zero] using hd
  simpa using scalarAC_variation α y (fun _ => 0) a b hy intervalIntegrable_const hder

end NLS.FunctionalAnalysis
