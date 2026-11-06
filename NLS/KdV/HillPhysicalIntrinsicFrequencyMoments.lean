import NLS.KdV.HillPhysicalFrequencyMoments
import NLS.KdV.HillIntrinsicFrequencyMoments

/-! # Equality of the physical and intrinsic canonical frequency moments

The original physical real-cut root equals the globally normalized
canonical product root on the intrinsic circle. No root sign or contour
normalization is left undetermined. Weighted natural-index sums agree
because the central weighted term is zero.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillPhysicalFrequencyMoment_eq_intrinsic (n : ℕ) (hn : 1≤n)
    (k : ℕ) (hk : 1≤k) (m : ℕ) :
    hillPhysicalFrequencyMoment q hq hr n hn k m=hillIntrinsicFrequencyMoment q hq hr n hn k m := by
  unfold hillPhysicalFrequencyMoment hillIntrinsicFrequencyMoment frequencyMoment
  apply circleIntegral.integral_congr
    (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1
      (hillRealGapContour_geometry q hq hr k hk).2.1.le)
  intro E hE
  dsimp only [hillL2ShiftedPrimitive]
  rw [hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr
    (hillRealGapContour_sphere_subset q hq hr k hk hE)]

theorem tsum_weighted_hillPhysicalFrequencyMoment_eq_intrinsic (n : ℕ) (hn : 1≤n) (m : ℕ) :
    (∑' k : ℕ, (k:ℂ)*hillPhysicalFrequencyMoment q hq hr n hn k m) =
      ∑' k : ℕ, (k:ℂ)*hillIntrinsicFrequencyMoment q hq hr n hn k m := by
  apply tsum_congr
  intro k
  by_cases hk : k=0
  · simp only [hk,Nat.cast_zero,zero_mul]
  · rw [hillPhysicalFrequencyMoment_eq_intrinsic q hq hr n hn k (by omega) m]

end NLS.KdV
