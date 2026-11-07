import NLS.KdV.PhysicalNativeFrequencyParameterization
import NLS.KdV.PhysicalFractionalQuotientBounds

/-! A diagonal-asymptotics dependency of Theorem 1.2(iii): BOTH actual
normalization quotients have fractional decay in the ORIGINAL native
H^(t-1) source norm. ONE physical chart precedes every decay exponent.
The complete diagonal moment/action remainder remains a further step. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem theorem_1_2_iii_diagonal_quotient_dependency
    (t : ℝ) (ht : 0≤t) (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q)) :
    ∃ A : PhysicalNativeFrequencyParameterization t ht, q∈A.domain ∧
      ∀ u : ℝ, 0≤u → u≤1 → u≤2*t → A.HasFractionalQuotientBounds u q := by
  obtain ⟨A,hqA⟩ := exists_physicalNativeFrequencyParameterization t ht q hq
  exact ⟨A,hqA,fun u hu0 hu1 hu2t => A.exists_fractional_quotient_bounds u hu0 hu1 hu2t q hqA hq⟩

end NLS.Articles.KdVKdV2Frequencies
