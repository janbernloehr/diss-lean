import NLS.SequenceSpaces.CriticalSobolevInclusion
import NLS.Fourier.PeriodicFourierLebesgueEndpoints

/-! # Critical Sobolev inclusion of original periodic distributions

This implements the finite-exponent inclusion from the introduction, printed p. 10.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

/-- Every original FL^p space at finite p>2 embeds continuously into H^(-1/2),
for any positive period, with the same distribution and coefficient normalization. -/
def criticalSobolevInclusion (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) :
    PeriodicFourierLebesgue L Weight.one (ENNReal.ofReal p) →L[ℂ]
      FourierLebesgueSpace L (-1/2) 2 :=
  (coefficientsIsometry (Weight.sobolev (-1/2)) 2
    (Weight.hasTemperedInverse_sobolev _)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((Coeff.criticalSobolevInclusion p hp).comp
        (unweightedCoefficients (ENNReal.ofReal p)).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem criticalSobolevInclusion_coefficient (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 < p) (u : PeriodicFourierLebesgue L Weight.one (ENNReal.ofReal p)) (n : ℤ) :
    (criticalSobolevInclusion p hp u).val (mode (-n)) = u.val (mode (-n)) := by
  change ((coefficientsIsometry (Weight.sobolev (-1/2)) 2
    (Weight.hasTemperedInverse_sobolev _))
      ((coefficientsIsometry (Weight.sobolev (-1/2)) 2
        (Weight.hasTemperedInverse_sobolev _)).symm
          (Coeff.criticalSobolevInclusion p hp (unweightedCoefficients _ u)))).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply,Coeff.criticalSobolevInclusion_apply,
    unweightedCoefficients_apply]

/-- The inclusion is the identity on actual original distributions. -/
theorem criticalSobolevInclusion_val (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 < p) (u : PeriodicFourierLebesgue L Weight.one (ENNReal.ofReal p)) :
    (criticalSobolevInclusion p hp u).val = u.val := by
  apply Distribution.ext_coefficients
  intro n
  exact criticalSobolevInclusion_coefficient p hp u n

theorem criticalSobolevInclusion_injective (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 < p) : Function.Injective (criticalSobolevInclusion (L := L) p hp) := by
  intro u v h
  apply Subtype.ext
  have he := congrArg Subtype.val h
  simpa only [criticalSobolevInclusion_val] using he

end NLS.Fourier.PeriodicFourierLebesgue
