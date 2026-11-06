import NLS.SequenceSpaces.ShiftedWeight

/-! # The unit spectral weight has exactly the coefficient norm -/

noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_toCoeff_one (q : WeightedCoeff SpectralWeight.one.toWeight p) :
    ‖SpectralWeight.one.toCoeff q‖ = ‖q‖ := by
  rw [WeightedCoeff.norm_eq]
  congr 1
  ext n
  simp only [SpectralWeight.toCoeff_apply,WeightedCoeff.weightEquiv_apply,
    SpectralWeight.one_apply,Complex.ofReal_one,one_mul]

end NLS.SpectralWeight
