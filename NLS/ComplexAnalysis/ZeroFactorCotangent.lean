import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Ring

/-! Full cotangent reduction at a zero scalar factor. The derivative
of the moving nonzero denominator is retained in the product rule
and vanishes with the scalar numerator at the basepoint. -/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fderiv_div_mul_of_zero (S K H : E → ℂ) (q : E)
    (hS : DifferentiableAt ℂ S q) (hK : DifferentiableAt ℂ K q)
    (hH : DifferentiableAt ℂ H q) (hKne : K q ≠ 0) (hzero : S q=0) :
    fderiv ℂ (fun p => (S p/K p)*H p) q = (H q/K q) • fderiv ℂ S q := by
  have he : (fun p => (S p/K p)*H p) = (fun p => S p*(H p/K p)) := by
    funext p
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  have hKi := (hasDerivAt_inv hKne).comp_hasFDerivAt q hK.hasFDerivAt
  have hHK : DifferentiableAt ℂ (fun p => H p/K p) q := by
    simpa only [Function.comp_def,div_eq_mul_inv] using (hH.hasFDerivAt.fun_mul hKi).differentiableAt
  have hd := hS.hasFDerivAt.fun_mul hHK.hasFDerivAt
  rw [hd.fderiv]
  ext v
  simp only [add_apply,smul_apply,smul_eq_mul,hzero,zero_mul,zero_add]

end NLS.ComplexAnalysis
