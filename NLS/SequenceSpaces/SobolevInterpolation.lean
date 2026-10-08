import NLS.SequenceSpaces.HilbertGeometricInterpolation
import NLS.SequenceSpaces.SobolevHomogeneous

/-! # Sharp Hilbert Sobolev interpolation

The inhomogeneous weight (1+|n|)^s is log-convex in s. Its interpolation
between L² and H^m has constant one and includes both endpoint orders.
-/
noncomputable section
namespace NLS.WeightedCoeff

/-- The magnitude of a weighted Fourier coefficient, with its exact real weight. -/
theorem norm_weightEquiv_sobolev (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) 2) (n : ℤ) :
    ‖weightEquiv (Weight.sobolev s) 2 a n‖ = (1+|(n:ℝ)|)^s*‖a.val n‖ := by
  rw [weightEquiv_apply,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (Weight.sobolev s |>.positive n).le,Weight.sobolev_apply]

/-- Every intermediate Sobolev norm is bounded by the exact geometric mean
of the L² and highest Sobolev norms. -/
theorem norm_sobolevInclusion_interpolate (m s : ℝ) (hm : 0 < m) (hs : 0 ≤ s) (hsm : s ≤ m)
    (a : WeightedCoeff (Weight.sobolev m) 2) :
    ‖sobolevInclusion hsm a‖ ≤ ‖sobolevToL2 hm.le a‖^(1-s/m)*‖a‖^(s/m) := by
  have ht : 0 ≤ s/m := div_nonneg hs hm.le
  have ht1 : s/m ≤ 1 := (div_le_one hm).mpr hsm
  change ‖weightEquiv (Weight.sobolev s) 2 (sobolevInclusion hsm a)‖ ≤
    ‖sobolevToL2 hm.le a‖^(1-s/m)*‖weightEquiv (Weight.sobolev m) 2 a‖^(s/m)
  apply Coeff.norm_le_geometric _ _ _ (s/m) ht ht1
  intro n
  rw [norm_weightEquiv_sobolev,norm_weightEquiv_sobolev,sobolevInclusion_apply,sobolevToL2_apply]
  rw [Real.mul_rpow (by positivity) (norm_nonneg _),← Real.rpow_mul (by positivity),
    mul_div_cancel₀ _ hm.ne']
  rw [mul_left_comm,← Real.rpow_add_of_nonneg (norm_nonneg _) (sub_nonneg.mpr ht1) ht]
  simp

end NLS.WeightedCoeff
