import NLS.SequenceSpaces.PairExponentEmbedding

/-! # Identity source exponent inclusion -/
noncomputable section
open scoped ENNReal
namespace NLS.CoeffPair

@[simp] theorem exponentInclusion_refl {p : ℝ≥0∞} [Fact (1 ≤ p)] (φ : CoeffPair p) :
    exponentInclusion (le_rfl : p ≤ p) φ = φ := by
  apply (toMax p).injective
  apply Prod.ext <;> ext k <;> rfl

end NLS.CoeffPair
