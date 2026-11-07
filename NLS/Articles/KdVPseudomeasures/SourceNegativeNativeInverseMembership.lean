import NLS.Articles.KdVPseudomeasures.SourceNegativeFractionalInverseRegularity
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeCompactFibers
import NLS.KdV.HillNativeRealCoordinateValue

/-! The proved original inverse regularity in the physical rough source
notation, retaining every raw native coefficient. -/
noncomputable section
open NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem hillReal_negative_sobolev_of_native_output (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (q : HillRealMeanZeroSource) (z : WeightedCoeff (Weight.signedSobolev (-r+1/2)) 2)
    (hz : ∀ k, z.val k = (hillRealSignedMap q).val.val.val k) :
    Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*q.val.val.val k) 2 := by
  have hcoords (k : ℤ) : z.val k =
      hillHminusNativeCoordinate k (originalPeriodOneCoefficients (originalHillPotentialOfRealSource q)) := by
    rw [originalHillPotentialOfRealSource_coefficients, ← hillRealSignedMap_apply_nativeCoordinate]
    exact hz k
  have hh := original_negative_sobolev_of_native_output r hr hr1 (originalHillPotentialOfRealSource q) z hcoords
  rwa [originalHillPotentialOfRealSource_coefficients] at hh

end NLS.Articles.KdVPseudomeasures
