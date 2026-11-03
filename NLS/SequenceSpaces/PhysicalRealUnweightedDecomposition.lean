import NLS.SequenceSpaces.PhysicalRealUnweightedProjection

/-! # The original physical real form is a genuine complexification -/
noncomputable section
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Coeff
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem physicalRealPart_complex_decomp (a : Coeff p) :
    a = (physicalRealPart p a).val+I • (physicalRealPart p ((-I) • a)).val := by
  ext n
  change a n = (physicalRealPart p a).val n+I*(physicalRealPart p ((-I) • a)).val n
  rw [physicalRealPart_apply,physicalRealPart_apply]
  change a n = (a n+conj (a (-n)))/2+I*(((-I)*a n+conj ((-I)*a (-n)))/2)
  rw [map_mul,map_neg,Complex.conj_I,neg_neg]
  linear_combination ((a n-conj (a (-n)))/2)*Complex.I_sq

end NLS.Coeff
