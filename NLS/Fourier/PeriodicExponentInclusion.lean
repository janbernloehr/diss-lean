import NLS.Fourier.PeriodicEndpointLowerInclusion
import NLS.SequenceSpaces.ExponentEmbedding

/-! Contractive exponent inclusion on original Fourier-Lebesgue spaces,
retaining the entire smooth-test distribution rather than only coefficients. -/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Increasing the Banach exponent preserves the original distribution. -/
def exponentInclusion (s : ℝ) (hpq : p ≤ q) :
    FourierLebesgueSpace L s p →L[ℂ] FourierLebesgueSpace L s q :=
  (sobolevCoefficients s q).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.exponentInclusion (Weight.sobolev s) hpq).comp
      (sobolevCoefficients s p).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Every raw original Fourier coefficient is retained. -/
theorem exponentInclusion_coefficient (s : ℝ) (hpq : p ≤ q) (f : FourierLebesgueSpace L s p) (k : ℤ) :
    (exponentInclusion s hpq f).val (mode (-k)) = f.val (mode (-k)) := by
  change ((sobolevCoefficients s q) ((sobolevCoefficients s q).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact WeightedCoeff.exponentInclusion_apply (Weight.sobolev s) hpq (sobolevCoefficients s p f) k

/-- The ENTIRE original physical distribution is unchanged. -/
theorem exponentInclusion_val (s : ℝ) (hpq : p ≤ q) (f : FourierLebesgueSpace L s p) :
    (exponentInclusion s hpq f).val = f.val := by
  apply Distribution.ext_coefficients
  exact exponentInclusion_coefficient s hpq f

/-- This inclusion is contractive in the exact original Fourier norms. -/
theorem norm_exponentInclusion_le (s : ℝ) (hpq : p ≤ q) (f : FourierLebesgueSpace L s p) :
    ‖exponentInclusion s hpq f‖ ≤ ‖f‖ := by
  change ‖(sobolevCoefficients s q).symm (WeightedCoeff.exponentInclusion _ hpq (sobolevCoefficients s p f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (WeightedCoeff.norm_exponentInclusion_le _ hpq _).trans_eq ((sobolevCoefficients s p).norm_map f)

end NLS.Fourier.PeriodicFourierLebesgue
