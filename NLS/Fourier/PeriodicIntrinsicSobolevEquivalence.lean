import NLS.Fourier.PeriodicIntrinsicSobolevEmbedding
import NLS.Fourier.IntrinsicSobolevEquivalence

/-!
# The interval Sobolev identification used in Lemma A.9

For 0<s<1/2, the intrinsic interval Sobolev Hilbert space is continuously
linearly equivalent to the original FL^{s,2} distribution space. Both directions
preserve the physical interval function and have explicit norm bounds. The
coefficient weight is exactly (1+|n|)^s; physical scaling stays in the constants.
The A.9 embedding and this equivalence give the same original distribution.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

namespace IntrinsicIntervalSobolev
open PeriodicFourierLebesgue
variable {s : ℝ}

/-- The genuine interval-to-original-periodic Sobolev equivalence below half regularity. -/
def originalSobolevEquiv (hs : 0 < s) (hs₁ : s < 1/2) :
    IntrinsicIntervalSobolev s L ≃L[ℂ] PeriodicFourierLebesgue L (Weight.sobolev s) 2 :=
  (weightedEquiv hs hs₁).trans
    (coefficientsIsometry (Weight.sobolev s) 2 (Weight.hasTemperedInverse_sobolev s)).symm.toContinuousLinearEquiv

/-- The equivalence preserves every normalized physical Fourier integral. -/
theorem originalSobolevEquiv_coefficient (hs : 0 < s) (hs₁ : s < 1/2)
    (f : IntrinsicIntervalSobolev s L) (n : ℤ) :
    (originalSobolevEquiv hs hs₁ f).val (mode (-n)) =
      intervalFourierCoefficient L (intervalPullback L f.val) n := by
  change (coefficientsIsometry (Weight.sobolev s) 2 (Weight.hasTemperedInverse_sobolev s)
    ((coefficientsIsometry (Weight.sobolev s) 2 (Weight.hasTemperedInverse_sobolev s)).symm
      (weightedEquiv hs hs₁ f))).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply,weightedEquiv_apply]

/-- The forward equivalence represents the original physical interval function. -/
theorem originalSobolevEquiv_val (hs : 0 < s) (hs₁ : s < 1/2) (f : IntrinsicIntervalSobolev s L) :
    (originalSobolevEquiv hs hs₁ f).val = Distribution.ofL1 (intervalPullback L f.val)
      (intervalIntegrable_of_memLp_two (memLp_intervalPullback (Fact.out : 0 < L) f.val)) := by
  apply Distribution.ext_coefficients
  intro n
  rw [originalSobolevEquiv_coefficient,Distribution.ofL1_coefficient]

/-- The forward norm bound retains the physical analysis constant. -/
theorem norm_originalSobolevEquiv_le (hs : 0 < s) (hs₁ : s < 1/2) (f : IntrinsicIntervalSobolev s L) :
    ‖originalSobolevEquiv hs hs₁ f‖ ≤ weightedAnalysisBoundConstant s L * ‖f‖ := by
  change ‖(coefficientsIsometry (Weight.sobolev s) 2 (Weight.hasTemperedInverse_sobolev s)).symm
    (weightedEquiv hs hs₁ f)‖ ≤ _
  simpa only [LinearIsometryEquiv.norm_map] using norm_weightedEquiv_le hs hs₁ f

/-- The inverse norm bound retains the physical synthesis constant. -/
theorem norm_originalSobolevEquiv_symm_le (hs : 0 < s) (hs₁ : s < 1/2)
    (u : PeriodicFourierLebesgue L (Weight.sobolev s) 2) :
    ‖(originalSobolevEquiv hs hs₁).symm u‖ ≤ weightedSynthesisBoundConstant s L * ‖u‖ := by
  change ‖(weightedEquiv hs hs₁).symm
    (coefficientsIsometry (Weight.sobolev s) 2 (Weight.hasTemperedInverse_sobolev s) u)‖ ≤ _
  simpa only [LinearIsometryEquiv.norm_map] using norm_weightedEquiv_symm_le hs hs₁
    (coefficientsIsometry (Weight.sobolev s) 2 (Weight.hasTemperedInverse_sobolev s) u)

/-- Arbitrary interval data maps to its original normalized distribution. -/
theorem originalSobolevEquiv_ofFunction_val (hs : 0 < s) (hs₁ : s < 1/2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 L)))
    (hE : fractionalIntervalEnergy s L f < ⊤) :
    (originalSobolevEquiv hs hs₁ (ofFunction f hf hE)).val =
      Distribution.ofL1 f (intervalIntegrable_of_memLp_two hf) := by
  apply Distribution.ext_coefficients
  intro n
  rw [originalSobolevEquiv_coefficient,Distribution.ofL1_coefficient,
    intervalFourierCoefficient_intervalPullback (Fact.out : 0 < L)]
  exact fourierCoeff_intervalL2Class (Fact.out : 0 < L) f hf n

/-- The inverse equivalence gives an actual interval representative of the original distribution. -/
theorem originalSobolevEquiv_symm_represents (hs : 0 < s) (hs₁ : s < 1/2)
    (u : PeriodicFourierLebesgue L (Weight.sobolev s) 2) :
    Distribution.ofL1 (intervalPullback L ((originalSobolevEquiv hs hs₁).symm u).val)
      (intervalIntegrable_of_memLp_two (memLp_intervalPullback (Fact.out : 0 < L) _)) = u.val := by
  rw [← originalSobolevEquiv_val hs hs₁,ContinuousLinearEquiv.apply_symm_apply]

/-- The A.9 embedding and Sobolev equivalence give the same original distribution. -/
theorem originalFourierEmbedding_eq_originalSobolevEquiv_val
    {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : 0 < s) (hs₁ : s < 1/2) (hq : 1/(s+1/2) < q) (f : IntrinsicIntervalSobolev s L) :
    (originalFourierEmbedding hs hs₁ hq f).val = (originalSobolevEquiv hs hs₁ f).val := by
  rw [originalFourierEmbedding_val,originalSobolevEquiv_val]
end IntrinsicIntervalSobolev
end NLS.Fourier
