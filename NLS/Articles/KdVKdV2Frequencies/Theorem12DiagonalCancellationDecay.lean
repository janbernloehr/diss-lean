import NLS.KdV.PhysicalNativeFrequencyParameterization
import NLS.KdV.PhysicalFractionalDiagonalCancellation

/-! The ACTUAL diagonal moment/action cancellation required for
Theorem 1.2(iii), in the ORIGINAL native Sobolev norm. The original +6I
counterterm is calibrated exactly; the full frequency remainder and
original action-space asymptotics remain separate obligations. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem theorem_1_2_iii_diagonal_cancellation_dependency
    (t : ℝ) (ht : 0≤t) (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q)) :
    ∃ A : PhysicalNativeFrequencyParameterization t ht, q∈A.domain ∧
      ∀ u : ℝ, 0≤u → u≤1 → u≤t → A.HasFractionalDiagonalCancellationBounds u q := by
  obtain ⟨A,hqA⟩ := exists_physicalNativeFrequencyParameterization t ht q hq
  exact ⟨A,hqA,fun u hu0 hu1 hut =>
    A.exists_fractional_diagonal_cancellation_bounds u hu0 hu1 hut q hqA hq⟩

end NLS.Articles.KdVKdV2Frequencies
