import NLS.ComplexAnalysis.ScalarDuhamel
import Mathlib.Analysis.Calculus.MeanValue

/-! # Global conservation and uniqueness for scalar coordinate equations -/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.ComplexAnalysis

theorem paired_scalar_evolution_product_constant (u v c : ℝ → ℂ)
    (hu : ∀ t, HasDerivAt u (c t*u t) t)
    (hv : ∀ t, HasDerivAt v (-c t*v t) t) (t : ℝ) :
    u t*v t=u 0*v 0 := by
  have hd (s : ℝ) : HasDerivAt (fun x => u x*v x) 0 s := by
    convert! (hu s).mul (hv s) using 1
    ring
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0

theorem global_scalar_evolution_eq_exp (c : ℂ) (u : ℝ → ℂ)
    (hu : ∀ t, HasDerivAt u (c*u t) t) (t : ℝ) :
    u t=Complex.exp (c*t)*u 0 := by
  have hd (s : ℝ) : HasDerivAt (fun x : ℝ => Complex.exp (-c*x)*u x) 0 s := by
    convert! (hasDerivAt_complex_exp_mul (-c) s).mul (hu s) using 1
    ring
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul] at he
  have hexp : Complex.exp (c*t)*Complex.exp (-c*t)=1 := by
    rw [←Complex.exp_add]
    have h : c*(t : ℂ)+ -c*t=0 := by ring
    rw [h,Complex.exp_zero]
  calc
    u t=Complex.exp (c*t)*(Complex.exp (-c*t)*u t) := by rw [←mul_assoc,hexp,one_mul]
    _=Complex.exp (c*t)*u 0 := by rw [he]

end NLS.ComplexAnalysis
