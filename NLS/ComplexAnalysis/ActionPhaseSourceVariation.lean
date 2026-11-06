import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- A stationary analytic amplitude times a rotating analytic phase has
this exact complex source derivative. -/
theorem actionPhase_fderiv_of_stationary_amplitude
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A θ : E → ℂ) (q h : E) (δ : ℂ)
    (hA : AnalyticAt ℂ A q) (hθ : AnalyticAt ℂ θ q)
    (hAzero : (fderiv ℂ A q) h=0) (hθsource : (fderiv ℂ θ q) h= -δ) :
    (fderiv ℂ (fun p => A p*Complex.exp (I*θ p)) q) h=
      -I*δ*(A q*Complex.exp (I*θ q)) := by
  have hd := hA.differentiableAt.hasFDerivAt.mul
    (hθ.differentiableAt.hasFDerivAt.const_mul I).cexp
  change HasFDerivAt (fun p => A p*Complex.exp (I*θ p)) _ q at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,hAzero,hθsource,mul_zero]
  ring

end NLS.ComplexAnalysis
