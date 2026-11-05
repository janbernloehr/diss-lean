import NLS.ComplexAnalysis.ScalarDuhamel
import Mathlib.Analysis.Calculus.MeanValue

/-! Exact global real-time solutions of a homogeneous scalar complex ODE. -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem eq_exp_mul_of_hasDerivAt (c : ℂ) (u : ℝ → ℂ)
    (hd : ∀ t, HasDerivAt u (c*u t) t) (t : ℝ) :
    u t=exp (c*t)*u 0 := by
  have hg (s : ℝ) : HasDerivAt (fun r : ℝ => exp (-c*r)*u r) 0 s := by
    convert! (hasDerivAt_complex_exp_mul (-c) s).mul (hd s) using 1
    ring
  have heq : exp (-c*t)*u t=exp (-c*(0:ℝ))*u 0 :=
    isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
      (fun s _ => (hg s).differentiableAt.differentiableWithinAt)
      (fun s _ => (hg s).deriv) (mem_univ t) (mem_univ 0)
  have he : exp (c*t)*exp (-c*t)=1 := by
    rw [← exp_add,neg_mul,add_neg_cancel,exp_zero]
  calc
    u t=exp (c*t)*(exp (-c*t)*u t) := by rw [← mul_assoc,he,one_mul]
    _=exp (c*t)*(exp (-c*(0:ℝ))*u 0) := congrArg (exp (c*t)*·) heq
    _=exp (c*t)*u 0 := by simp

end NLS.ComplexAnalysis
