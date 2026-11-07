import NLS.KdV.FreeHillRegularity
import NLS.KdV.PseudomeasurePerturbation
import NLS.Fourier.PeriodicDistributionConvolutionProduct
import NLS.Fourier.PeriodicSobolevDuality
import NLS.Fourier.PeriodicH1Multiplication
import NLS.SequenceSpaces.WeightedWeakStarLowerTopology

/-! # The endpoint reduced inverse on the original Hill domain

For every source spectral weight and `r < 1/2`, the reduced inverse maps
weighted endpoint data to the original period-two H1 distribution space.
The previously constructed endpoint perturbation is the absolutely convergent
Fourier product of q with this original H1 element and agrees with the actual
H-minus-one multiplication operator defined by physical H1 duality.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The multiplier bound retains the arbitrary source spectral weight. -/
theorem endpointReducedHillResolvent_weight_bound (w : SpectralWeight) (r : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    w.negativeSobolev (r-2) k * ‖reducedHillSymbol n hn z hz k‖ ≤
      (4+2*‖z‖) * w.negativeSobolev r k := by
  rw [w.negativeSobolev_sub r 2 k, mul_assoc]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (sobolev_two_reducedHillSymbol_bound n hn z hz k) ((w.negativeSobolev r).positive k).le

/-- The exact two-derivative gain on arbitrary signed spectral weights and
every Banach exponent, including infinity. -/
def endpointReducedHillResolventGain {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : SpectralWeight) (r : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    WeightedCoeff (w.negativeSobolev r) p →L[ℂ]
      WeightedCoeff (w.negativeSobolev (r-2)) p :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun k => reducedHillSymbol n hn z hz k)
    (4+2*‖z‖) (by positivity) (endpointReducedHillResolvent_weight_bound w r n hn z hz)

@[simp] theorem endpointReducedHillResolventGain_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : SpectralWeight) (r : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (f : WeightedCoeff (w.negativeSobolev r) p) (k : ℤ) :
    (endpointReducedHillResolventGain w r n hn z hz f).val k =
      reducedHillSymbol n hn z hz k * f.val k := rfl

/-- The derivative gain has a finite operator bound at each spectral point. -/
theorem norm_endpointReducedHillResolventGain_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : SpectralWeight) (r : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (f : WeightedCoeff (w.negativeSobolev r) p) :
    ‖endpointReducedHillResolventGain w r n hn z hz f‖ ≤ (4+2*‖z‖)*‖f‖ :=
  WeightedCoeff.norm_weightedMultiplier_le _ _ _ _ (by positivity)
    (endpointReducedHillResolvent_weight_bound w r n hn z hz) f

/-- The strict source range is exactly sufficient for the gained endpoint
space to embed into the H1 Hilbert domain. -/
theorem endpoint_resolvent_H1_threshold (r : ℝ) (hr : r < 1/2) :
    1 < (-(r-2)-1)*(2:ℝ≥0∞).toReal := by
  norm_num
  linarith

/-- The reduced inverse, on endpoint data, taking values in the actual H1
coefficient domain rather than a formal sequence of improved growth. -/
def endpointReducedHillResolventH1 (w : SpectralWeight) (r : ℝ) (hr : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    WeightedCoeff (w.negativeSobolev r) ⊤ →L[ℂ] WeightedCoeff (Weight.sobolev 1) 2 :=
  (WeightedCoeff.endpointLowerInclusion (-(r-2)) 1 (by norm_num)
    (endpoint_resolvent_H1_threshold r hr)).comp
      ((w.negativeSobolevToSobolev (r-2) ⊤).comp
        (endpointReducedHillResolventGain w r n hn z hz))

@[simp] theorem endpointReducedHillResolventH1_apply (w : SpectralWeight) (r : ℝ) (hr : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (f : WeightedCoeff (w.negativeSobolev r) ⊤) (k : ℤ) :
    (endpointReducedHillResolventH1 w r hr n hn z hz f).val k =
      reducedHillSymbol n hn z hz k * f.val k := by
  simp only [endpointReducedHillResolventH1, ContinuousLinearMap.comp_apply,
    WeightedCoeff.endpointLowerInclusion_apply, SpectralWeight.negativeSobolevToSobolev_apply,
    endpointReducedHillResolventGain_apply]

/-- The same reduced inverse with values in original period-two H1 distributions. -/
def endpointReducedHillResolventH1Original (w : SpectralWeight) (r : ℝ) (hr : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    WeightedCoeff (w.negativeSobolev r) ⊤ →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  (sobolevCoefficients 1 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (endpointReducedHillResolventH1 w r hr n hn z hz)

/-- The actual H1 distribution retains the exact original resolvent coefficients. -/
theorem endpointReducedHillResolventH1Original_coefficient (w : SpectralWeight)
    (r : ℝ) (hr : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (f : WeightedCoeff (w.negativeSobolev r) ⊤) (k : ℤ) :
    (endpointReducedHillResolventH1Original w r hr n hn z hz f).val (mode (-k)) =
      reducedHillSymbol n hn z hz k * f.val k := by
  change ((sobolevCoefficients 1 2) ((sobolevCoefficients 1 2).symm
    (endpointReducedHillResolventH1 w r hr n hn z hz f))).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply, endpointReducedHillResolventH1_apply]

/-- Original distributions for all source weighted endpoint coefficients. -/
def endpointHillDistribution (w : SpectralWeight) (r : ℝ)
    (a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ :=
  (coefficientsIsometry _ _ (w.hasTemperedInverse_negativeSobolev r)).symm a

@[simp] theorem endpointHillDistribution_coefficient (w : SpectralWeight) (r : ℝ)
    (a : WeightedCoeff (w.negativeSobolev r) ⊤) (k : ℤ) :
    (endpointHillDistribution w r a).val (mode (-k)) = a.val k := by
  change ((coefficientsIsometry _ _ (w.hasTemperedInverse_negativeSobolev r))
    ((coefficientsIsometry _ _ (w.hasTemperedInverse_negativeSobolev r)).symm a)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- Every endpoint datum in the strict source range is an original
H-minus-one distribution, with a bounded linear inclusion. -/
def endpointHillHminusOne (w : SpectralWeight) (r : ℝ) (hr : r < 1/2) :
    WeightedCoeff (w.negativeSobolev r) ⊤ →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  (sobolevCoefficients (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.endpointLowerInclusion (-r) (-1) (by norm_num) (by
      norm_num
      linarith)).comp (w.negativeSobolevToSobolev r ⊤))

@[simp] theorem endpointHillHminusOne_coefficient (w : SpectralWeight) (r : ℝ)
    (hr : r < 1/2) (f : WeightedCoeff (w.negativeSobolev r) ⊤) (k : ℤ) :
    (endpointHillHminusOne w r hr f).val (mode (-k)) = f.val k := by
  change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (WeightedCoeff.endpointLowerInclusion_apply (-r) (-1) (p := 2) (by norm_num)
    (by norm_num; linarith) (w.negativeSobolevToSobolev r ⊤ f) k).trans
      (w.negativeSobolevToSobolev_apply r ⊤ f k)

/-- The H-minus-one inclusion preserves the entire original distribution. -/
theorem endpointHillHminusOne_val (w : SpectralWeight) (r : ℝ) (hr : r < 1/2)
    (f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    (endpointHillHminusOne w r hr f).val = (endpointHillDistribution w r f).val := by
  apply Distribution.ext_coefficients
  intro k
  rw [endpointHillHminusOne_coefficient, endpointHillDistribution_coefficient]

/-- The newly obtained H1 resolvent and the old same-space resolvent are
literally the same original distribution on every smooth periodic test. -/
theorem endpointReducedHillResolventH1Original_val (w : SpectralWeight)
    (r : ℝ) (hr : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    (endpointReducedHillResolventH1Original w r hr n hn z hz f).val =
      (endpointHillDistribution w r
        (weightedReducedHillResolvent (w.negativeSobolev r) n hn z hz f)).val := by
  apply Distribution.ext_coefficients
  intro k
  rw [endpointReducedHillResolventH1Original_coefficient, endpointHillDistribution_coefficient,
    weightedReducedHillResolvent_apply]
  change (if k.natAbs = n then (0:ℂ) else _) * f.val k = _
  split_ifs <;> simp

/-- The endpoint perturbation is a genuinely convergent Fourier product of
original distributions, and its resolvent factor lies in the H1 domain. -/
theorem endpointHillPerturbation_hasFourierProduct (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    Distribution.HasFourierProduct (endpointHillDistribution w r q).val
      (endpointReducedHillResolventH1Original w r hr1 n hn z hz f).val
      (endpointHillDistribution w r
        (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q f)).val := by
  intro m
  have hs := summable_norm_endpointHill_terms w r hr hr1 n hn z hz q
    (w.negativeShiftEquiv r hr (n:ℤ) ⊤ f) m
  simp only [SpectralWeight.negativeShiftEquiv_apply] at hs
  simp only [endpointHillDistribution_coefficient,
    endpointReducedHillResolventH1Original_coefficient,
    unshiftedEndpointHillPerturbation_apply, ← mul_assoc]
  exact hs.of_norm.hasSum

/-- The endpoint Fourier perturbation equals actual multiplication by the
singular potential after the original H1 reduced inverse. This is equality
of original H-minus-one distributions, hence of their full smooth-test action. -/
theorem endpointHillPerturbation_physical (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointHillHminusOne w r hr1
      (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q f) =
        hminusOneMultiplication (endpointHillHminusOne w r hr1 q)
          (endpointReducedHillResolventH1Original w r hr1 n hn z hz f) := by
  apply Subtype.ext
  rw [endpointHillHminusOne_val, hminusOneMultiplication_apply]
  have hP := hasFourierProduct_hminusOneProduct (endpointHillHminusOne w r hr1 q)
    (endpointReducedHillResolventH1Original w r hr1 n hn z hz f)
  rw [endpointHillHminusOne_val] at hP
  exact (endpointHillPerturbation_hasFourierProduct w r hr hr1 n hn z hz q f).unique hP

/-- The identification is an equality of bounded operators on the original
endpoint source, rather than only a compatibility of formal coefficients. -/
theorem endpointHillPerturbation_physicalOperator (w : SpectralWeight)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) :
    (endpointHillHminusOne w r hr1).comp
      (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q) =
        (hminusOneMultiplication (endpointHillHminusOne w r hr1 q)).comp
          (endpointReducedHillResolventH1Original w r hr1 n hn z hz) := by
  ext f
  exact endpointHillPerturbation_physical w r hr hr1 n hn z hz q f

end NLS.KdV
