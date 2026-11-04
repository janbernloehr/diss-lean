import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Source derivatives determined by agreement along a real line -/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Complex source derivatives agree in a direction whenever the functions
agree on its real line near the base. Differentiability alone suffices. -/
theorem fderiv_apply_eq_of_real_line_eventuallyEq
    (F G : E → ℂ) (q v : E)
    (hF : DifferentiableAt ℂ F q) (hG : DifferentiableAt ℂ G q)
    (he : ∀ᶠ t : ℝ in 𝓝 0, F (q+(t : ℂ) • v)=G (q+(t : ℂ) • v)) :
    (fderiv ℂ F q) v=(fderiv ℂ G q) v := by
  have hsmul : HasDerivAt (fun z : ℂ => z • v) v 0 := by
    simpa only [one_smul,id_eq] using (hasDerivAt_id (0 : ℂ)).smul_const v
  have hline : HasDerivAt (fun z : ℂ => q+z • v) v 0 := by
    exact hsmul.const_add q
  have hF0 : HasFDerivAt F (fderiv ℂ F q) (q+(0 : ℂ) • v) := by simpa using hF.hasFDerivAt
  have hG0 : HasFDerivAt G (fderiv ℂ G q) (q+(0 : ℂ) • v) := by simpa using hG.hasFDerivAt
  have hdF := (hF0.comp_hasDerivAt 0 hline).comp_ofReal
  have hdG := (hG0.comp_hasDerivAt 0 hline).comp_ofReal
  have heq : (fun t : ℝ => F (q+(t : ℂ) • v)) =ᶠ[𝓝 0] (fun t : ℝ => G (q+(t : ℂ) • v)) := he
  exact hdF.deriv.symm.trans (heq.deriv_eq.trans hdG.deriv)

end NLS.ComplexAnalysis
