import NLS.ComplexAnalysis.RealLineDerivativeUniqueness
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Conjugate derivatives determined by a physical real line -/
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped ComplexConjugate
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Nearby conjugate values along a real line determine conjugate complex
source derivatives in that direction. No reality off that line is assumed. -/
theorem fderiv_conjugate_of_real_line_eventuallyEq
    (F G : E → ℂ) (q v : E)
    (hF : DifferentiableAt ℂ F q) (hG : DifferentiableAt ℂ G q)
    (he : ∀ᶠ t : ℝ in 𝓝 0, F (q+(t:ℂ) • v)=conj (G (q+(t:ℂ) • v))) :
    (fderiv ℂ F q) v=conj ((fderiv ℂ G q) v) := by
  have hline : HasDerivAt (fun z : ℂ => q+z • v) v 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0:ℂ)).smul_const v).const_add q
  have hF0 : HasFDerivAt F (fderiv ℂ F q) (q+(0:ℂ) • v) := by simpa using hF.hasFDerivAt
  have hG0 : HasFDerivAt G (fderiv ℂ G q) (q+(0:ℂ) • v) := by simpa using hG.hasFDerivAt
  have hdF := (hF0.comp_hasDerivAt 0 hline).comp_ofReal
  have hdG := (hG0.comp_hasDerivAt 0 hline).comp_ofReal
  exact hdF.unique (hdG.star.congr_of_eventuallyEq he)

end NLS.ComplexAnalysis
