import NLS.ComplexAnalysis.ScalarDuhamel
import Mathlib.Analysis.Calculus.MeanValue

/-! # Global uniqueness for a scalar complex phase equation -/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.Dynamics

/-- The integrating factor identifies every everywhere differentiable
solution, in both time directions, with the exact exponential phase. -/
theorem eq_exp_mul_of_hasDerivAt (c : ℂ) (u : ℝ → ℂ)
    (hu : ∀ t : ℝ, HasDerivAt u (c*u t) t) (t : ℝ) :
    u t = exp (c*t)*u 0 := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => exp (-c*r)*u r) 0 s := by
    convert! (NLS.ComplexAnalysis.hasDerivAt_complex_exp_mul (-c) s).mul (hu s) using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  have he : exp (c*t)*exp (-c*t) = 1 := by
    rw [← exp_add,show c*(t:ℂ)+ -c*t = 0 by ring,exp_zero]
  calc
    u t = exp (c*t)*(exp (-c*t)*u t) := by rw [← mul_assoc,he,one_mul]
    _ = exp (c*t)*(exp (-c*(0:ℝ))*u 0) := congrArg (exp (c*t)*·) hc
    _ = exp (c*t)*u 0 := by simp

end NLS.Dynamics
