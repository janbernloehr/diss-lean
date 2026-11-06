import NLS.ComplexAnalysis.ParametricCosinePrimitive
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Differentiating the genuine moving cosine terminal equation in a
stationary midpoint/half-length direction gives its exact terminal variation. -/
theorem cosineTerminal_fderiv_of_stationary_gap
    (τ δ μ ε : A → ℂ) (p h : A)
    (hτ : AnalyticAt ℂ τ p) (hδ : AnalyticAt ℂ δ p)
    (hμ : AnalyticAt ℂ μ p) (hε : AnalyticAt ℂ ε p)
    (heq : ∀ᶠ b in 𝓝 p, cosineGapPoint (τ b) (δ b) (ε b)=μ b)
    (hτzero : (fderiv ℂ τ p) h=0) (hδzero : (fderiv ℂ δ p) h=0) :
    (fderiv ℂ μ p) h=-(δ p*Complex.sin (ε p))*((fderiv ℂ ε p) h) := by
  have hc := (Complex.hasDerivAt_cos (ε p)).comp_hasFDerivAt p hε.differentiableAt.hasFDerivAt
  have hd := hτ.differentiableAt.hasFDerivAt.fun_add (hδ.differentiableAt.hasFDerivAt.fun_mul hc)
  change HasFDerivAt (𝕜 := ℂ) (fun b : A => cosineGapPoint (τ b) (δ b) (ε b)) _ p at hd
  have he : (fun b : A => cosineGapPoint (τ b) (δ b) (ε b))=ᶠ[𝓝 p] μ := heq
  have hu := (hd.congr_of_eventuallyEq he.symm).unique hμ.differentiableAt.hasFDerivAt
  have hv := congrArg (fun L : A →L[ℂ] ℂ => L h) hu
  simp only [add_apply,smul_apply,smul_eq_mul,hτzero,hδzero,mul_zero,zero_add,add_zero] at hv
  linear_combination -hv

end NLS.ComplexAnalysis
