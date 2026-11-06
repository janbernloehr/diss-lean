import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



theorem traceRoot_fderiv_eq_zero_of_trace_kernel
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R T : E → ℂ) (p h : E) (hR : AnalyticAt ℂ R p) (hT : AnalyticAt ℂ T p)
    (heq : ∀ᶠ q in 𝓝 p, R q^2=T q^2-4) (hne : R p≠0)
    (hker : (fderiv ℂ T p) h=0) : (fderiv ℂ R p) h=0 := by
  have hdR := hR.differentiableAt.hasFDerivAt.mul hR.differentiableAt.hasFDerivAt
  have hdT := (hT.differentiableAt.hasFDerivAt.mul hT.differentiableAt.hasFDerivAt).sub_const 4
  have hform : (fun q => R q*R q)=ᶠ[𝓝 p] (fun q => T q*T q-4) := by
    filter_upwards [heq] with q hq
    simpa only [pow_two] using hq
  have hu := (hdR.congr_of_eventuallyEq hform.symm).unique hdT
  have hv := congrArg (fun L : E →L[ℂ] ℂ => L h) hu
  simp only [add_apply,smul_apply,smul_eq_mul,hker,mul_zero,zero_add] at hv
  have hz : (2*R p)*((fderiv ℂ R p) h)=0 := by linear_combination hv
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hne)

end NLS.ComplexAnalysis
