import NLS.ZakharovShabat.HigherSobolevH1Realization
import NLS.ZakharovShabat.SourceSobolevNormalizedCoordinates

/-! # First-order normalized coordinates of higher Sobolev sources

A continuous linear map sends the original Hm source, m >= 1, to normalized first-order coordinates. Decoding recovers the original potential exactly and preserves the real source locus.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- Continuous normalized H1 coordinates of every original higher Sobolev source. -/
def higherSobolevFirstNormalizedCoordinates (m : ℕ) (hm : 1 ≤ m) : SobolevSource m →L[ℂ] CoeffPair 2 :=
  sobolevNormalizedCoordinates.toContinuousLinearMap.comp
    ((hierarchySobolevToScalarDomain m hm).prodMap (hierarchySobolevToScalarDomain m hm))

/-- The first-order decoder preserves the original higher Sobolev source exactly. -/
theorem normalizedWeightedSource_higherSobolevFirstNormalizedCoordinates (m : ℕ) (hm : 1 ≤ m)
    (a : SobolevSource m) :
    normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num))
      (higherSobolevFirstNormalizedCoordinates m hm a) = higherSobolevSourceInclusion m a := by
  change normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num))
    (sobolevNormalizedCoordinates (higherSobolevToH1 m hm a)) = _
  rw [normalizedWeightedSource_sobolevNormalizedCoordinates,sobolevSourceInclusion_higherSobolevToH1]

/-- Real higher Sobolev sources give real normalized first-order coordinates. -/
theorem higherSobolevFirstNormalizedCoordinates_realType (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    IsRealType (CoeffPair.toMax 2 (higherSobolevFirstNormalizedCoordinates m hm a.val)) := by
  apply (sobolevNormalizedCoordinates_realType_iff (higherSobolevToH1 m hm a.val)).2
  rw [sobolevSourceInclusion_higherSobolevToH1]
  exact a.property

end NLS.ZakharovShabat
