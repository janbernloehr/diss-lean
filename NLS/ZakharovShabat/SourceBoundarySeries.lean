import NLS.ZakharovShabat.SourceBoundarySpaces
import NLS.Fourier.PairDistributionInfty

/-!
# Boundary-mode series in the original spaces

Every boundary element has unique weighted scalar amplitudes. The printed
series converges in the original norm for finite exponents, and as actual
periodic tempered distributions for every Banach exponent, including infinity.
Its modes are the actual exponential waves, with the boundary sign and reversed
first-component frequency. No infinity-norm convergence is asserted.
-/

noncomputable section
open scoped ENNReal SchwartzMap FourierTransform
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A unit raw Fourier coefficient at frequency n, independent of the weight. -/
def sourceWeightedSingle (s : ℝ) (n : ℤ) : WeightedCoeff (Weight.sobolev s) p :=
  (WeightedCoeff.weightEquiv (Weight.sobolev s) p).symm
    (lp.single p n (Weight.sobolev s n : ℂ))

omit [Fact (1 ≤ p)] in
/-- The raw coefficient of the weighted single mode. -/
theorem sourceWeightedSingle_apply (s : ℝ) (n k : ℤ) :
    (sourceWeightedSingle (p := p) s n).val k = if k = n then 1 else 0 := by
  classical
  change (lp.single (E := fun _ : ℤ => ℂ) p n (Weight.sobolev s n : ℂ)) k / (Weight.sobolev s k : ℂ) = _
  by_cases h : k = n
  · subst k
    simp only [lp.single_apply, Pi.single_eq_same, if_true, div_self (Weight.complex_ne_zero _ _)]
  · simp [lp.single_apply, h]

/-- Every finite-exponent weighted sequence is its norm-convergent Fourier series. -/
theorem hasSum_sourceWeightedSingle (hp : p ≠ ⊤) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    HasSum (fun n : ℤ => a.val n • sourceWeightedSingle s n) a := by
  have h := (WeightedCoeff.weightIsometry (Weight.sobolev s) p).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum
    (lp.hasSum_single hp (WeightedCoeff.weightEquiv (Weight.sobolev s) p a))
  convert h using 1
  · funext n
    change a.val n • (WeightedCoeff.weightEquiv (Weight.sobolev s) p).symm _ =
      (WeightedCoeff.weightEquiv (Weight.sobolev s) p).symm _
    rw [← map_smul, ← lp.single_smul]
    congr 2
    simp [WeightedCoeff.weightEquiv_apply, mul_comm]
  · exact ((WeightedCoeff.weightEquiv (Weight.sobolev s) p).symm_apply_apply a).symm

/-- The printed unnormalized boundary mode in the original weighted space. -/
def sourceWeightedBoundaryMode (b : BoundaryCondition) (s : ℝ) (n : ℤ) :
    sourceWeightedBoundarySubspace (p := p) b s :=
  sourceWeightedBoundaryAmplitudeEquiv b s (sourceWeightedSingle s n)

/-- The printed boundary-mode expansion converges in the original norm for finite p. -/
theorem hasSum_sourceWeightedBoundaryModes (hp : p ≠ ⊤) (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    HasSum (fun n : ℤ => a.val n • sourceWeightedBoundaryMode b s n)
      (sourceWeightedBoundaryAmplitudeEquiv b s a) := by
  let L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] sourceWeightedBoundarySubspace (p := p) b s :=
    (sourceWeightedBoundaryAmplitudeEquiv b s).toContinuousLinearMap
  have h := L.hasSum (hasSum_sourceWeightedSingle hp s a)
  convert h using 1
  · funext n
    exact (L.map_smul (a.val n) (sourceWeightedSingle s n)).symm
  · rfl

/-- An actual periodic tempered distribution representing a single exponential wave. -/
def sourceWaveDistribution (n : ℤ) : 𝓢'(ℝ, ℂ) := distributionSynthesis (lp.single 2 n 1)

/-- The wave acts by sampling the Fourier transform of the Schwartz test. -/
theorem sourceWaveDistribution_apply (n : ℤ) (g : 𝓢(ℝ, ℂ)) :
    sourceWaveDistribution n g = (𝓕 g) (-(n : ℝ) / 2) := by
  rw [sourceWaveDistribution, distributionSynthesis_single, one_mul, ← fourier_sample_eq_integral_wave]

/-- Weighted scalar Fourier series converge as distributions for all Banach exponents. -/
theorem hasSum_sourceWaveDistribution (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) p) :
    HasSum (fun n : ℤ => a.val n • sourceWaveDistribution n) (sobolevDistributionSynthesisCLM s a) := by
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  intro g
  have h := (summable_norm_weightedDistributionSynthesis (Weight.sobolev s)
    (Weight.hasTemperedInverse_sobolev s) a g).of_norm.hasSum
  simpa only [HasSum, sum_apply, smul_apply,
    smul_eq_mul, sourceWaveDistribution_apply, sobolevDistributionSynthesisCLM_apply] using h

/-- The actual pair of periodic distributions represented by the boundary amplitudes. -/
def sourceBoundaryDistribution (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) :=
  (sobolevDistributionSynthesisCLM s (b.extensionSign • WeightedCoeff.reflection s a),
    sobolevDistributionSynthesisCLM s a)

/-- The signed pair of actual wave distributions in the printed boundary basis. -/
def sourceBoundaryDistributionMode (b : BoundaryCondition) (n : ℤ) : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) :=
  (b.extensionSign • sourceWaveDistribution (-n), sourceWaveDistribution n)

/-- The boundary-mode series converges as distributions, including at infinity. -/
theorem hasSum_sourceBoundaryDistribution (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    HasSum (fun n : ℤ => a.val n • sourceBoundaryDistributionMode b n)
      (sourceBoundaryDistribution b s a) := by
  have h₁ := (Equiv.neg ℤ).hasSum_iff.mpr
    (hasSum_sourceWaveDistribution s (b.extensionSign • WeightedCoeff.reflection s a))
  have h₂ := hasSum_sourceWaveDistribution s a
  convert HasSum.prodMk h₁ h₂ using 1
  · funext n
    simp [sourceBoundaryDistributionMode, WeightedCoeff.smul_val, WeightedCoeff.reflection_apply,
      smul_smul, mul_comm]
  · rfl

/-- The series sum is the actual synthesis of the original finite-exponent coefficient pair. -/
theorem sourceBoundaryDistribution_eq_sourcePair (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) :
    ((sobolevDistributionSynthesisCLM s).prodMap (sobolevDistributionSynthesisCLM s))
      (WeightedCoeffPair.toMax (Weight.sobolev s) p
        (sourceWeightedBoundaryAmplitudeEquiv b s a).val) = sourceBoundaryDistribution b s a := by
  rw [sourceWeightedBoundaryAmplitudeEquiv_apply]
  rfl

/-- The infinity series sum synthesizes the original signed coupled-supremum coefficients. -/
theorem sourceBoundaryDistribution_eq_sourcePairInfty (b : BoundaryCondition) (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) ⊤) :
    pairDistributionInftyCLM s (sourceWeightedBoundaryAmplitudeEquivInfty b s a).val =
      sourceBoundaryDistribution b s a := by
  rw [sourceWeightedBoundaryAmplitudeEquivInfty_apply]
  change (sobolevDistributionSynthesisCLM s (WeightedCoeff.reflection s (b.extensionSign • a)),
    sobolevDistributionSynthesisCLM s a) = _
  rw [map_smul]
  rfl

/-- Weighted single coefficients synthesize the same actual exponential wave. -/
theorem sourceWeightedSingle_distribution (s : ℝ) (n : ℤ) :
    sobolevDistributionSynthesisCLM s (sourceWeightedSingle (p := p) s n) = sourceWaveDistribution n := by
  apply weightedDistributionSynthesis_eq_distributionSynthesis
  intro k
  simpa [lp.single_apply, Pi.single_apply, eq_comm] using sourceWeightedSingle_apply (p := p) s n k

/-- Reflection reverses the frequency of a single raw mode. -/
theorem sourceWeightedSingle_reflection (s : ℝ) (n : ℤ) :
    WeightedCoeff.reflection s (sourceWeightedSingle (p := p) s n) = sourceWeightedSingle s (-n) := by
  apply Subtype.ext
  funext k
  simp only [WeightedCoeff.reflection_apply, sourceWeightedSingle_apply]
  simp [neg_eq_iff_eq_neg]

/-- The coefficient-space and distributional boundary modes agree. -/
theorem sourceBoundaryDistribution_single (b : BoundaryCondition) (s : ℝ) (n : ℤ) :
    sourceBoundaryDistribution b s (sourceWeightedSingle (p := p) s n) =
      sourceBoundaryDistributionMode b n := by
  simp only [sourceBoundaryDistribution, sourceWeightedSingle_reflection, map_smul,
    sourceWeightedSingle_distribution, sourceBoundaryDistributionMode]

/-- The modes act by the ordinary integrals of the printed physical waves. -/
theorem sourceBoundaryDistributionMode_physical (b : BoundaryCondition) (n : ℤ) (g : 𝓢(ℝ, ℂ)) :
    ((sourceBoundaryDistributionMode b n).1 g, (sourceBoundaryDistributionMode b n).2 g) =
      (b.extensionSign * ∫ x : ℝ, wave (-n) x * g x, ∫ x : ℝ, wave n x * g x) := by
  change (b.extensionSign * distributionSynthesis (lp.single 2 (-n) 1) g,
    distributionSynthesis (lp.single 2 n 1) g) = _
  rw [distributionSynthesis_single, distributionSynthesis_single]
  simp only [one_mul]

end NLS.ZakharovShabat
