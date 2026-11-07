import NLS.KdV.HillHalfNativeMaps
import NLS.KdV.SingularHillResolventFamily

/-! Faithful inclusion of the full original rough-potential Sobolev scale
into the native H-minus-one base. No source distribution is changed. -/
noncomputable section
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- Interpret the complete rough-potential coefficient space in the native base. -/
def hillHalfPotentialBase (r : ℝ) (hr1 : r ≤ 1) :
    WeightedCoeff (Weight.sobolev (-r)) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  (sobolevCoefficients (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (WeightedCoeff.sobolevInclusion (by linarith : (-1:ℝ) ≤ -r))

/-- Every raw coefficient of the entire potential is unchanged. -/
theorem hillHalfPotentialBase_coefficient (r : ℝ) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (k : ℤ) :
    (hillHalfPotentialBase r hr1 q).val (mode (-k)) = q.val k := by
  change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact WeightedCoeff.sobolevInclusion_apply (by linarith : (-1:ℝ) ≤ -r) q k

/-- The original rough-potential Sobolev norm controls its native base norm. -/
theorem norm_hillHalfPotentialBase_le (r : ℝ) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) : ‖hillHalfPotentialBase r hr1 q‖ ≤ ‖q‖ := by
  change ‖(sobolevCoefficients (-1) 2).symm (WeightedCoeff.sobolevInclusion _ q)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact WeightedCoeff.norm_sobolevInclusion_le _ q

/-- The corresponding bounded map on the ENTIRE original physical Sobolev space. -/
def hillSobolevBaseInclusion (r : ℝ) (hr1 : r ≤ 1) :
    FourierLebesgueSpace (2:ℝ) (-r) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  (hillHalfPotentialBase r hr1).comp
    (sobolevCoefficients (-r) 2).toContinuousLinearEquiv.toContinuousLinearMap

/-- Inclusion retains the identical ENTIRE original physical distribution. -/
theorem hillSobolevBaseInclusion_val (r : ℝ) (hr1 : r ≤ 1)
    (q : FourierLebesgueSpace (2:ℝ) (-r) 2) : (hillSobolevBaseInclusion r hr1 q).val = q.val := by
  apply Distribution.ext_coefficients
  intro k
  exact hillHalfPotentialBase_coefficient r hr1 (sobolevCoefficients (-r) 2 q) k

/-- The native inclusion is contractive in the exact original Sobolev norms. -/
theorem norm_hillSobolevBaseInclusion_le (r : ℝ) (hr1 : r ≤ 1)
    (q : FourierLebesgueSpace (2:ℝ) (-r) 2) : ‖hillSobolevBaseInclusion r hr1 q‖ ≤ ‖q‖ := by
  exact (norm_hillHalfPotentialBase_le r hr1 (sobolevCoefficients (-r) 2 q)).trans_eq
    ((sobolevCoefficients (-r) 2).norm_map q)

end NLS.KdV
