import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- A nonvanishing analytic square root is stationary in every
source direction in which its actual square is stationary. -/
theorem squareRoot_source_fderiv_eq_zero
    {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
    (R F : A → ℂ) (p h : A) (hR : AnalyticAt ℂ R p) (hF : AnalyticAt ℂ F p)
    (heq : ∀ᶠ b in 𝓝 p, R b^2=F b) (hne : R p≠0)
    (hzero : (fderiv ℂ F p) h=0) : (fderiv ℂ R p) h=0 := by
  have hd := hR.differentiableAt.hasFDerivAt.mul hR.differentiableAt.hasFDerivAt
  have he : (fun b => R b*R b)=ᶠ[𝓝 p] F := by
    filter_upwards [heq] with b hb
    simpa only [pow_two] using hb
  have hu := (hd.congr_of_eventuallyEq he.symm).unique hF.differentiableAt.hasFDerivAt
  have hv := congrArg (fun L : A →L[ℂ] ℂ => L h) hu
  simp only [add_apply,smul_apply,smul_eq_mul,hzero] at hv
  have hz : (2*R p)*((fderiv ℂ R p) h)=0 := by linear_combination hv
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hne)

end NLS.ComplexAnalysis
