import NLS.Fourier.PeriodicWienerAlgebra
import NLS.SequenceSpaces.SobolevConstant

/-!
# Lemma A.8: the original Sobolev-to-Wiener embedding

At every finite Banach exponent, FL^{1,p} embeds continuously into FL¹ without
changing the underlying original distribution. The norm uses the exact weight
(1+|n|), and the product bound includes the inverse-weight Hölder constant C_p,
with C_p ≤ 2p. The printed constant-one bound (A.4) is false; see
`SobolevProductCounterexample` for finite-polynomial witnesses.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier
open SmoothPeriodicTest
namespace PeriodicFourierLebesgue
variable {L : ℝ} [Fact (0 < L)]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The continuous inclusion FL^{1,p} → FL¹ for every finite Banach exponent. -/
def sobolevToWiener (hp : p ≠ ⊤) :
    PeriodicFourierLebesgue L (Weight.sobolev 1) p →L[ℂ] PeriodicFourierLebesgue L Weight.one 1 :=
  (unweightedCoefficients 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.sobolevToL1CLM p hp).comp
      (coefficientsIsometry (Weight.sobolev 1) p (Weight.hasTemperedInverse_sobolev 1)).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The Sobolev inclusion preserves every normalized Fourier coefficient. -/
theorem sobolevToWiener_coefficient (hp : p ≠ ⊤)
    (u : PeriodicFourierLebesgue L (Weight.sobolev 1) p) (n : ℤ) :
    (sobolevToWiener hp u).val (mode (-n)) = u.val (mode (-n)) := by
  rw [← unweightedCoefficients_apply]
  change unweightedCoefficients 1 ((unweightedCoefficients 1).symm
    (WeightedCoeff.sobolevToL1CLM p hp (coefficientsIsometry (Weight.sobolev 1) p (Weight.hasTemperedInverse_sobolev 1) u))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply,WeightedCoeff.sobolevToL1CLM_apply]
  rfl

/-- The inclusion preserves the entire original distribution, not only its coefficients. -/
theorem sobolevToWiener_val (hp : p ≠ ⊤)
    (u : PeriodicFourierLebesgue L (Weight.sobolev 1) p) : (sobolevToWiener hp u).val = u.val := by
  apply Distribution.ext_coefficients
  exact sobolevToWiener_coefficient hp u

/-- The original Sobolev-to-Wiener inclusion is injective. -/
theorem sobolevToWiener_injective (hp : p ≠ ⊤) : Function.Injective (sobolevToWiener (L := L) hp) := by
  intro u v huv
  apply Subtype.ext
  simpa only [sobolevToWiener_val] using congrArg Subtype.val huv

/-- The inclusion bound with the inverse-weight Hölder constant. -/
theorem norm_sobolevToWiener_le (hp : p ≠ ⊤)
    (u : PeriodicFourierLebesgue L (Weight.sobolev 1) p) :
    ‖sobolevToWiener hp u‖ ≤ WeightedCoeff.sobolevEmbeddingConstant p hp * ‖u‖ := by
  change ‖(unweightedCoefficients 1).symm (WeightedCoeff.sobolevToL1CLM p hp
    (coefficientsIsometry (Weight.sobolev 1) p (Weight.hasTemperedInverse_sobolev 1) u))‖ ≤ _
  simpa only [LinearIsometryEquiv.norm_map] using
    WeightedCoeff.norm_sobolevToL1CLM_le p hp (coefficientsIsometry (Weight.sobolev 1) p (Weight.hasTemperedInverse_sobolev 1) u)

/-- A simple explicit bound for the inclusion constant at any finite exponent. -/
theorem norm_sobolevToWiener_le_two_mul (hp : p ≠ ⊤)
    (u : PeriodicFourierLebesgue L (Weight.sobolev 1) p) :
    ‖sobolevToWiener hp u‖ ≤ (2*p.toReal)*‖u‖ :=
  (norm_sobolevToWiener_le hp u).trans
    (mul_le_mul_of_nonneg_right (WeightedCoeff.sobolevEmbeddingConstant_le_two_mul p hp) (norm_nonneg _))

/-- The synthesized continuous function represents the original Sobolev distribution. -/
theorem sobolevToWiener_continuous_represents (hp : p ≠ ⊤)
    (u : PeriodicFourierLebesgue L (Weight.sobolev 1) p) :
    Distribution.ofContinuous (continuousRepresentative (sobolevToWiener hp u)) = u.val := by
  rw [continuousRepresentative_represents,sobolevToWiener_val]

/-- Multiplication of an original FL^{1,p} element by an original FLᵖ element. -/
def sobolevProduct (hp : p ≠ ⊤) (u : PeriodicFourierLebesgue L (Weight.sobolev 1) p)
    (v : PeriodicFourierLebesgue L Weight.one p) : PeriodicFourierLebesgue L Weight.one p :=
  youngProduct (show YoungRelation 1 p p by simp [YoungRelation]) (sobolevToWiener hp u) v

/-- The Sobolev product retains the exact normalized convolution formula. -/
theorem sobolevProduct_coefficient (hp : p ≠ ⊤) (u : PeriodicFourierLebesgue L (Weight.sobolev 1) p)
    (v : PeriodicFourierLebesgue L Weight.one p) (n : ℤ) :
    (sobolevProduct hp u v).val (mode (-n)) = ∑' k : ℤ, u.val (mode (-(n-k))) * v.val (mode (-k)) := by
  simp only [sobolevProduct,youngProduct_coefficient,sobolevToWiener_coefficient]

/-- The corrected form of (A.4), including the required Hölder constant. -/
theorem norm_sobolevProduct_le (hp : p ≠ ⊤) (u : PeriodicFourierLebesgue L (Weight.sobolev 1) p)
    (v : PeriodicFourierLebesgue L Weight.one p) :
    ‖sobolevProduct hp u v‖ ≤ WeightedCoeff.sobolevEmbeddingConstant p hp * ‖u‖ * ‖v‖ :=
  (norm_youngProduct_le _ _ _).trans
    (mul_le_mul_of_nonneg_right (norm_sobolevToWiener_le hp u) (norm_nonneg _))


end PeriodicFourierLebesgue
end NLS.Fourier
