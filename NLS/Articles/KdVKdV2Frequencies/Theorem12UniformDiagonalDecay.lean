import NLS.KdV.PhysicalNativeFrequencyParameterization
import NLS.KdV.PhysicalUniformDiagonalCancellation

/-! Theorem 1.2(iii)'s actual diagonal dependency, uniformly on one
full complex neighborhood in the ORIGINAL native H^(t-1) norm. -/
noncomputable section
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem theorem_1_2_iii_native_uniform_diagonal_dependency
    (t : ℝ) (ht : 0<t) (ht1 : t<1) (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht.le q)) :
    ∃ A : PhysicalNativeFrequencyParameterization t ht.le, q ∈ A.domain ∧
      ∃ T : Set (WeightedCoeff (Weight.sobolev (t-1)) 2),
        IsOpen T ∧ q ∈ T ∧ T ⊆ A.domain ∧
          ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a ∈ T, ∀ n : ℕ+, K ≤ (n:ℤ).natAbs →
            Weight.sobolev (3*t-1) (n:ℤ)*‖A.diagonalRemainder n a‖ ≤ ε := by
  obtain ⟨A,hqA⟩ := exists_physicalNativeFrequencyParameterization t ht.le q hq
  exact ⟨A,hqA,A.exists_uniform_sharp_diagonal_cancellation_decay ht ht1 q hqA hq⟩

end NLS.Articles.KdVKdV2Frequencies
