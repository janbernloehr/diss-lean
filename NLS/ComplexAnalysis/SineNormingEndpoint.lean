import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



/-- At a zero norming coordinate, an analytic sine terminal has its cotangent
in the norming span; variations of the analytic prefactor disappear. -/
theorem sineTerminal_fderiv_eq_norming_of_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ε A G : E → ℂ) (q : E)
    (hε : AnalyticAt ℂ ε q) (hA : AnalyticAt ℂ A q) (hG : AnalyticAt ℂ G q)
    (hG0 : G q=0) (hcos : Complex.cos (ε q)≠0)
    (hrel : (fun p => Complex.sin (ε p))=ᶠ[𝓝 q] (fun p => A p*Complex.sinh (G p))) :
    fderiv ℂ ε q=(A q/Complex.cos (ε q)) • fderiv ℂ G q := by
  have hleft := hε.differentiableAt.hasFDerivAt.csin
  have hright := hA.differentiableAt.hasFDerivAt.mul hG.differentiableAt.hasFDerivAt.csinh
  have he := hleft.unique (hright.congr_of_eventuallyEq hrel)
  apply ContinuousLinearMap.ext
  intro h
  have hv := congrArg (fun L : E →L[ℂ] ℂ => L h) he
  simp only [smul_apply,add_apply,smul_eq_mul,hG0,Complex.sinh_zero,Complex.cosh_zero,
    zero_mul,one_mul,add_zero] at hv
  change (fderiv ℂ ε q) h=(A q/Complex.cos (ε q))*(fderiv ℂ G q) h
  calc
    _ = (A q*(fderiv ℂ G q) h)/Complex.cos (ε q) :=
      (eq_div_iff hcos).mpr (by simpa only [mul_comm] using hv)
    _ = _ := by ring

end NLS.ComplexAnalysis
