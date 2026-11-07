import NLS.KdV.HillPeriodOnePotential

noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.KdV

/-- The original Fourier Sobolev norm for every real exponent, with the
literal factor 2*pi and a convergent sum, rather than a comparable norm. -/
theorem hillPeriodOne_real_sobolev_norm_sq (s : ℝ) (hs : 0 ≤ s)
    (p : WeightedCoeff (SpectralWeight.piSobolev s hs).doubleIndex.toWeight 2) :
    HasSum (fun k : ℤ => (1+|2*Real.pi*(k : ℝ)|)^(2*s)*‖p.val k‖^2) (‖p‖^2) := by
  have he (k : ℤ) :
      ‖WeightedCoeff.weightEquiv (SpectralWeight.piSobolev s hs).doubleIndex.toWeight 2 p k‖^2 =
        (1+|2*Real.pi*(k : ℝ)|)^(2*s)*‖p.val k‖^2 := by
    rw [hillPeriodOne_weighted_coefficient_sq,← SpectralWeight.doubleIndex_apply,
      hillPeriodOneSobolevWeight,← Real.rpow_mul_natCast (by positivity)]
    congr 2
    norm_num
    ring
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,he,← WeightedCoeff.norm_eq] using
    lp.hasSum_norm (p := 2) (by norm_num)
      (WeightedCoeff.weightEquiv (SpectralWeight.piSobolev s hs).doubleIndex.toWeight 2 p)

end NLS.KdV
