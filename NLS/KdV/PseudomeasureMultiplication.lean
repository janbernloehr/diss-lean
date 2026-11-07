import NLS.KdV.PseudomeasureRegularity
import NLS.SequenceSpaces.SignedSobolevConvolution

/-! # Endpoint multiplication on the full physical H1 domain

For every potential of order -r, 0<=r<1/2, multiplication of every H1
input has order -r in the infinity norm. This is a proved regularity result
for the main theorem's unweighted endpoint space, not an extra domain
hypothesis in the spectral reduction.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The exact H1-to-Wiener-r summability threshold. -/
theorem endpoint_H1_Wiener_threshold (r : ℝ) (hr : r < 1/2) :
    1 < (1-r)*(2:ℝ≥0∞).toReal := by norm_num; linarith

/-- All original H1 data lie in the regular Wiener space needed for the
signed convolution estimate. -/
def endpointH1ToWiener (r : ℝ) (hr : r < 1/2) :
    FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] WeightedCoeff (Weight.sobolev r) 1 :=
  (WeightedCoeff.sobolevHolderInclusion (p := 2) (r := 2) (q := 1)
    1 r (by norm_num) (endpoint_H1_Wiener_threshold r hr)).comp
      (sobolevCoefficients 1 2).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem endpointH1ToWiener_apply (r : ℝ) (hr : r < 1/2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) (k : ℤ) :
    (endpointH1ToWiener r hr f).val k = f.val (mode (-k)) :=
  WeightedCoeff.sobolevHolderInclusion_apply (p := 2) (r := 2) (q := 1)
    1 r (by norm_num) (endpoint_H1_Wiener_threshold r hr) (sobolevCoefficients 1 2 f) k

/-- Multiplication by every endpoint potential on the entire original H1 domain,
taking values in the original endpoint coefficient space. -/
def endpointH1Multiplication (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ]
      WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  (WeightedCoeff.signedSobolevConvolutionCLM r hr q).comp (endpointH1ToWiener r hr1)

/-- Its original Fourier formula is inherited from the absolutely convergent Banach series. -/
theorem endpointH1Multiplication_apply (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) (m : ℤ) :
    (endpointH1Multiplication r hr hr1 q f).val m =
      ∑' k : ℤ, q.val (m-k)*f.val (mode (-k)) := by
  simp only [endpointH1Multiplication, ContinuousLinearMap.comp_apply,
    WeightedCoeff.signedSobolevConvolutionCLM_apply, WeightedCoeff.signedSobolevConvolution_apply,
    endpointH1ToWiener_apply]

/-- This endpoint realization is precisely the physical product defined by
the full original H1/H-minus-one duality. -/
theorem endpointH1Multiplication_physical (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    endpointHillHminusOne SpectralWeight.one r hr1 (endpointH1Multiplication r hr hr1 q f) =
      hminusOneMultiplication (endpointHillHminusOne SpectralWeight.one r hr1 q) f := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro m
  rw [endpointHillHminusOne_coefficient, hminusOneMultiplication_apply,
    hminusOneProduct_coefficient, endpointH1Multiplication_apply]
  simp only [endpointHillHminusOne_coefficient]

/-- The already bounded source tail perturbation is multiplication after the
physical reduced inverse, also as an equality in the endpoint normed space. -/
theorem endpointH1Multiplication_resolvent (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    (endpointH1Multiplication r hr hr1 q).comp
      (endpointReducedHillResolventH1Original SpectralWeight.one r hr1 n hn z hz) =
      unshiftedEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q := by
  ext a
  apply Subtype.ext
  funext m
  change (endpointH1Multiplication r hr hr1 q
    (endpointReducedHillResolventH1Original SpectralWeight.one r hr1 n hn z hz a)).val m = _
  rw [endpointH1Multiplication_apply, unshiftedEndpointHillPerturbation_apply]
  apply tsum_congr
  intro k
  rw [endpointReducedHillResolventH1Original_coefficient]
  ring

end NLS.KdV
