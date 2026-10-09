import NLS.ComplexAnalysis.OscillatoryIntegralParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Exact constant-potential oscillatory integrals -/
noncomputable section
open Set MeasureTheory
namespace NLS.ComplexAnalysis

/-- Constant inputs retain the exact endpoint exponential difference. -/
theorem oscillatoryIntegral_const (c : ℂ) (hc : c ≠ 0) (t : ℝ) (a : ℂ) :
    oscillatoryIntegral c t (fun _ => a) =
      (Complex.exp (c*t)-Complex.exp (-c*t))*a/(2*c) := by
  have hf : AbsolutelyContinuousOnInterval (fun _ : ℝ => a) 0 t :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have h := oscillatoryIntegral_parts c t (fun _ => a) hf (by simp)
  have hz : oscillatoryIntegral c t (fun _ => (0 : ℂ)) = 0 := by
    simp [oscillatoryIntegral]
  have hd : deriv (fun _ : ℝ => a) = fun _ => 0 := by funext r; simp
  rw [hd,hz,add_zero] at h
  apply (eq_div_iff (mul_ne_zero (by norm_num) hc)).mpr
  calc
    _ = (2*c)*oscillatoryIntegral c t (fun _ => a) := mul_comm _ _
    _ = _ := h
    _ = _ := by ring

/-- Changing the sign of the kernel frequency has no effect on a constant input. -/
theorem oscillatoryIntegral_neg_const (c : ℂ) (hc : c ≠ 0) (t : ℝ) (a : ℂ) :
    oscillatoryIntegral (-c) t (fun _ => a) = oscillatoryIntegral c t (fun _ => a) := by
  rw [oscillatoryIntegral_const _ (neg_ne_zero.mpr hc),oscillatoryIntegral_const _ hc]
  simp only [neg_neg]
  ring

/-- A quarter-period computation used to test the interval-norm convention. -/
theorem oscillatoryIntegral_const_quarter_period :
    oscillatoryIntegral (Complex.I*(2*Real.pi)) (1/4) (fun _ => (1 : ℂ)) =
      (1/(2*Real.pi) : ℝ) := by
  have hc : Complex.I*(2*Real.pi) ≠ (0 : ℂ) := by
    exact mul_ne_zero Complex.I_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [oscillatoryIntegral_const _ hc]
  have hp : (Complex.I*(2*Real.pi))*(↑(1/4 : ℝ)) = (Real.pi : ℂ)/2*Complex.I := by
    push_cast
    ring
  have hm : -(Complex.I*(2*Real.pi))*(↑(1/4 : ℝ)) = -(Real.pi : ℂ)/2*Complex.I := by
    push_cast
    ring
  rw [hp,hm,Complex.exp_pi_div_two_mul_I,Complex.exp_neg_pi_div_two_mul_I]
  push_cast
  field_simp
  ring

end NLS.ComplexAnalysis
