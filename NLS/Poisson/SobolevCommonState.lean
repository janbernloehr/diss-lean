import NLS.Poisson.ConjugateSobolevBracket
import NLS.Fourier.ArbitraryPeriodDistribution

/-! # A common physical state in conjugate Sobolev domains

For finite exponents, the intersection is a closed submodule of the two original Banach domains.
Its two coefficient representatives agree at every signed frequency, hence
synthesize the same pair of actual distributions on every positive period.
This supplies the shared base point for the source Poisson bracket.
-/
noncomputable section
open scoped ENNReal SchwartzMap
namespace NLS.Poisson
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The original signed raw coefficients as a continuous map into the product topology. -/
def rawSignedCoefficientsCLM (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] (ℤ → ℂ × ℂ) :=
  ContinuousLinearMap.pi (fun n =>
    ((WeightedCoeff.evalCLM (Weight.sobolev s) p n).comp
      ((ContinuousLinearMap.fst ℂ _ _).comp (WeightedCoeffPair.toMax (Weight.sobolev s) p).toContinuousLinearMap)).prod
    ((WeightedCoeff.evalCLM (Weight.sobolev s) p n).comp
      ((ContinuousLinearMap.snd ℂ _ _).comp (WeightedCoeffPair.toMax (Weight.sobolev s) p).toContinuousLinearMap)))

@[simp] theorem rawSignedCoefficientsCLM_apply (s : ℝ) (a : WeightedCoeffPair (Weight.sobolev s) p) (n : ℤ) :
    rawSignedCoefficientsCLM s p a n = (a.fst.val n,a.snd.val n) := rfl

/-- Equality of the two signed Fourier representatives. -/
def commonStateConstraint (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    (WeightedCoeffPair (Weight.sobolev (-s)) q × WeightedCoeffPair (Weight.sobolev s) p) →L[ℂ] (ℤ → ℂ × ℂ) :=
  (rawSignedCoefficientsCLM (-s) q).comp (ContinuousLinearMap.fst ℂ _ _) -
    (rawSignedCoefficientsCLM s p).comp (ContinuousLinearMap.snd ℂ _ _)

/-- An intersection of the coefficient domains, with both original norms at finite exponents. -/
def commonStateSubmodule (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :
    Submodule ℂ (WeightedCoeffPair (Weight.sobolev (-s)) q × WeightedCoeffPair (Weight.sobolev s) p) :=
  (commonStateConstraint s p q).ker

abbrev SobolevCommonState (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] :=
  ↥(commonStateSubmodule s p q)

instance (s : ℝ) : CompleteSpace (SobolevCommonState s p q) :=
  (commonStateConstraint s p q).isClosed_ker.completeSpace_coe

/-- The intersection norm is the maximum of its two coefficient-space norms. -/
theorem norm_commonState (s : ℝ) (x : SobolevCommonState s p q) :
    ‖x‖ = max ‖x.val.1‖ ‖x.val.2‖ := rfl

/-- The two source representatives agree coefficient by coefficient. -/
theorem commonState_coefficients (s : ℝ) (x : SobolevCommonState s p q) (n : ℤ) :
    x.val.1.fst.val n = x.val.2.fst.val n ∧ x.val.1.snd.val n = x.val.2.snd.val n := by
  have h := congrArg (fun a : ℤ → ℂ × ℂ => a n) x.property
  change (x.val.1.fst.val n,x.val.1.snd.val n) - (x.val.2.fst.val n,x.val.2.snd.val n) = 0 at h
  have he := sub_eq_zero.mp h
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

/-- Every pair of equal representatives gives a point of the intersection. -/
def commonStateOfCoefficients (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev (-s)) q) (b : WeightedCoeffPair (Weight.sobolev s) p)
    (h : ∀ n, a.fst.val n = b.fst.val n ∧ a.snd.val n = b.snd.val n) : SobolevCommonState s p q :=
  ⟨(a,b),by
    change commonStateConstraint s p q (a,b) = 0
    ext n
    · exact sub_eq_zero.mpr (h n).1
    · exact sub_eq_zero.mpr (h n).2⟩

/-- Continuous inclusion into the first original source domain. -/
def commonStateLeftCLM (s : ℝ) :
    SobolevCommonState s p q →L[ℂ] WeightedCoeffPair (Weight.sobolev (-s)) q :=
  (ContinuousLinearMap.fst ℂ _ _).comp (commonStateSubmodule s p q).subtypeL

/-- Continuous inclusion into the second original source domain. -/
def commonStateRightCLM (s : ℝ) :
    SobolevCommonState s p q →L[ℂ] WeightedCoeffPair (Weight.sobolev s) p :=
  (ContinuousLinearMap.snd ℂ _ _).comp (commonStateSubmodule s p q).subtypeL

/-- Synthesize a signed pair as actual periodic distributions at any positive period. -/
def signedPairDistributionCLM (L : ℝ) (hL : 0 < L) (s : ℝ) :
    WeightedCoeffPair (Weight.sobolev s) p →L[ℂ] (𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ)) :=
  ((Fourier.arbitraryPeriodDistributionSynthesisCLM L hL (Weight.sobolev s)
    (Weight.hasTemperedInverse_sobolev s)).prodMap
    (Fourier.arbitraryPeriodDistributionSynthesisCLM L hL (Weight.sobolev s)
      (Weight.hasTemperedInverse_sobolev s))).comp
  (((WeightedCoeff.reflection s).toContinuousLinearEquiv.toContinuousLinearMap.prodMap
    (ContinuousLinearMap.id ℂ _)).comp (WeightedCoeffPair.toMax (Weight.sobolev s) p).toContinuousLinearMap)

@[simp] theorem signedPairDistributionCLM_apply (L : ℝ) (hL : 0 < L) (s : ℝ)
    (a : WeightedCoeffPair (Weight.sobolev s) p) :
    signedPairDistributionCLM L hL s a =
      (Fourier.arbitraryPeriodDistributionSynthesis L hL (Weight.sobolev s)
          (Weight.hasTemperedInverse_sobolev s) (WeightedCoeff.reflection s a.fst),
        Fourier.arbitraryPeriodDistributionSynthesis L hL (Weight.sobolev s)
          (Weight.hasTemperedInverse_sobolev s) a.snd) := rfl

/-- The common state really is the same physical pair on every positive period. -/
theorem commonState_distribution_eq (L : ℝ) (hL : 0 < L) (s : ℝ) (x : SobolevCommonState s p q) :
    signedPairDistributionCLM L hL (-s) x.val.1 = signedPairDistributionCLM L hL s x.val.2 := by
  simp only [signedPairDistributionCLM_apply]
  apply Prod.ext
  · apply Fourier.periodicDistribution_ext_arbitraryPeriod L hL
      (Fourier.arbitraryPeriodDistributionSynthesis_periodic L hL _ _ _)
      (Fourier.arbitraryPeriodDistributionSynthesis_periodic L hL _ _ _)
    intro n
    simp only [Fourier.arbitraryPeriodDistributionSynthesis_coefficient,WeightedCoeff.reflection_apply]
    exact (commonState_coefficients s x (-n)).1
  · apply Fourier.periodicDistribution_ext_arbitraryPeriod L hL
      (Fourier.arbitraryPeriodDistributionSynthesis_periodic L hL _ _ _)
      (Fourier.arbitraryPeriodDistributionSynthesis_periodic L hL _ _ _)
    intro n
    simp only [Fourier.arbitraryPeriodDistributionSynthesis_coefficient]
    exact (commonState_coefficients s x n).2

end NLS.Poisson
