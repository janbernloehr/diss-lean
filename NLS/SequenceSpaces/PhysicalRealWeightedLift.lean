import NLS.SequenceSpaces.PhysicalRealWeightEquivalence
import NLS.SequenceSpaces.PhysicalRealUnweightedCoefficients

/-! # Weighted representatives of physical real coefficient sequences -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- Weighted membership produces a physical real weighted representative
of the exact original coefficients, without choosing a new source. -/
theorem exists_physicalReal_weighted_coefficients (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : Coeff.physicalRealSubmodule p)
    (ha : Memℓp (fun n : ℤ => (w n : ℂ)*a.val n) p) :
    ∃ b : physicalRealSubmodule w p, ∀ n : ℤ, b.val.val n = a.val n :=
  ⟨⟨⟨fun n => a.val n,ha⟩,fun n => a.property n⟩,fun _ => rfl⟩

end NLS.WeightedCoeff
