import NLS.SequenceSpaces.WeightedNonnegativeActions

/-! # Transporting cone neighborhoods through the complex weighting map -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem weightNormalization_coe_eq (w : Weight) (p : ℝ≥0∞) [Fact (1≤p)] :
    ((weightIsometry w p).toContinuousLinearEquiv : WeightedCoeff w p → Coeff p) = weightEquiv w p := rfl

theorem weightNormalization_nonnegative (w : Weight) (p : ℝ≥0∞) [Fact (1≤p)]
    (a : WeightedCoeff w p) (ha : a ∈ nonnegativeLocus w p) :
    (weightIsometry w p).toContinuousLinearEquiv a ∈ Coeff.nonnegativeLocus p :=
  (mem_nonnegativeLocus_iff w p a).mp ha

end NLS.WeightedCoeff
