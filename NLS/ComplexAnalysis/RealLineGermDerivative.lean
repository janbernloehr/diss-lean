import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Agreement along a genuine real affine line determines the complex
source derivative in that line's direction. -/
theorem fderiv_eq_of_eventuallyEq_real_affine_line
    (F G : A → ℂ) (p h : A) (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (heq : ∀ᶠ t : ℝ in 𝓝 0, F (p+(t : ℂ) • h)=G (p+(t : ℂ) • h)) :
    (fderiv ℂ F p) h=(fderiv ℂ G p) h := by
  have hline : HasDerivAt (fun z : ℂ => p+z • h) h 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add p
  have hF0 : DifferentiableAt ℂ F (p+(0 : ℂ) • h) := by simpa only [zero_smul,add_zero] using hF.differentiableAt
  have hG0 : DifferentiableAt ℂ G (p+(0 : ℂ) • h) := by simpa only [zero_smul,add_zero] using hG.differentiableAt
  have hdF := (hF0.hasFDerivAt.comp_hasDerivAt 0 hline).comp_ofReal
  have hdG := (hG0.hasFDerivAt.comp_hasDerivAt 0 hline).comp_ofReal
  have he : (fun t : ℝ => F (p+(t : ℂ) • h))=ᶠ[𝓝 0] (fun t : ℝ => G (p+(t : ℂ) • h)) := heq
  have hu := (hdF.congr_of_eventuallyEq he.symm).unique hdG
  simpa only [zero_smul,add_zero] using hu

end NLS.ComplexAnalysis
