import NLS.Fourier.PeriodicSobolevDuality
import NLS.SequenceSpaces.WeightedWeakStarLowerTopology

/-! # Original pseudomeasures embedded in lower weighted distribution spaces

The exact condition is (s-t)*p>1 with finite p>=1. The inclusion preserves
the entire original distribution, not just a compatible coefficient norm.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact endpoint-to-lower-space inclusion on original distributions. -/
def endpointLowerInclusion (s t : ℝ) (hp : p ≠ ⊤) (h : 1 < (s-t)*p.toReal) :
    FourierLebesgueSpace L s ⊤ →L[ℂ] FourierLebesgueSpace L t p :=
  (sobolevCoefficients t p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.endpointLowerInclusion s t hp h).comp
      (sobolevCoefficients s ⊤).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Every normalized original Fourier coefficient is unchanged. -/
theorem endpointLowerInclusion_coefficient (s t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (s-t)*p.toReal) (u : FourierLebesgueSpace L s ⊤) (n : ℤ) :
    (endpointLowerInclusion s t hp h u).val (mode (-n)) = u.val (mode (-n)) := by
  change ((sobolevCoefficients t p)
    ((sobolevCoefficients t p).symm
      (WeightedCoeff.endpointLowerInclusion s t hp h (sobolevCoefficients s ⊤ u)))).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply, WeightedCoeff.endpointLowerInclusion_apply]
  rfl

/-- The inclusion is literally the same original smooth-test distribution. -/
theorem endpointLowerInclusion_val (s t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (s-t)*p.toReal) (u : FourierLebesgueSpace L s ⊤) :
    (endpointLowerInclusion s t hp h u).val = u.val := by
  apply Distribution.ext_coefficients
  exact endpointLowerInclusion_coefficient s t hp h u

theorem endpointLowerInclusion_injective (s t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (s-t)*p.toReal) : Function.Injective (endpointLowerInclusion (L := L) s t hp h) := by
  intro u v huv
  apply Subtype.ext
  simpa only [endpointLowerInclusion_val] using congrArg Subtype.val huv

end NLS.Fourier.PeriodicFourierLebesgue
