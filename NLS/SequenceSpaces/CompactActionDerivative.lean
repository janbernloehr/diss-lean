import NLS.SequenceSpaces.Pitt
import NLS.SequenceSpaces.RefinedActionDerivative

/-! # Compact derivatives of analytic refined action corrections -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- Pitt's theorem makes the corrected derivative compact whenever the
analytic correction has a strictly smaller Banach sequence target. -/
theorem isCompactOperator_actionCorrection_fderiv (hq : q ≠ ⊤) (hrq : r < q)
    (V : Set (Coeff q)) (hV : IsOpen V) (F : Coeff q → Coeff q) (H : Coeff q → Coeff r)
    (hF : AnalyticOnNhd ℂ F V) (hH : AnalyticOnNhd ℂ H V)
    (he : ∀ b ∈ V, ∀ n, H b n = F b n+2*b n) (b : Coeff q) (hb : b ∈ V) :
    IsCompactOperator (fderiv ℂ F b+(2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff q)) := by
  rw [actionCorrection_fderiv_factorization hrq.le V hV F H hF hH he b hb]
  exact (isCompactOperator_of_exponent_lt hq hrq (fderiv ℂ H b)).clm_comp (exponentInclusion hrq.le)

end NLS.Coeff
