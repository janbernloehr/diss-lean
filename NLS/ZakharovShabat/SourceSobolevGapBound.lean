import NLS.ZakharovShabat.SourceSobolevEmbedding
import NLS.ZakharovShabat.SourceWeightedGapBound

/-! # Locally bounded weighted squared gaps on the full H¹ source -/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- The squared gap with the physical Sobolev weight at its resonant index. -/
def sourceSobolevWeightedSquaredGap (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) : ℂ :=
  sourceWeightedSquaredGap (SpectralWeight.sobolev 1 (by norm_num)) sobolevSourceInclusion a n

/-- Every H¹ source has a neighborhood on which the actual weighted squared gaps
have uniformly bounded ℓ¹ norm. No finite-gap or real-type hypothesis is required. -/
theorem exists_local_sourceSobolevWeightedSquaredGap_bound (a : ScalarDomain 2 × ScalarDomain 2) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a ∈ U ∧
      ∃ C : ℝ, ∀ b ∈ U, ∃ g : Coeff 1,
        (∀ n : ℤ, g n = sourceSobolevWeightedSquaredGap b n) ∧ ‖g‖ ≤ C :=
  exists_local_sourceWeightedSquaredGap_bound (SpectralWeight.sobolev 1 (by norm_num))
    sobolevSourceInclusion sobolevSourceWeightedPeriodOne
    weightedBaseToPair_sobolevSourceWeightedPeriodOne a

end NLS.ZakharovShabat
