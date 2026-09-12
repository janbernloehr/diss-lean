import NLS.SequenceSpaces.WeightedPairNormInfty
import NLS.Fourier.WeightedDistributionIdentification

/-!
# Genuine distribution pairs with the source's infinity norm

The first signed pair coefficient has opposite scalar Fourier frequency.
Synthesis preserves that convention and the norm is recovered from the actual
distributional coefficients, at every real Sobolev regularity.
-/

noncomputable section
open scoped ENNReal SchwartzMap
namespace NLS.Fourier

/-- Synthesize the source's signed endpoint pair as two actual periodic distributions. -/
def pairDistributionInftyCLM (s : ℝ) : WeightedCoeffPairInfty (Weight.sobolev s) →L[ℂ]
    𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) :=
  ((sobolevDistributionSynthesisCLM s (p := ⊤)).prodMap (sobolevDistributionSynthesisCLM s)).comp
    (WeightedCoeffPairInfty.toScalarMax s).toContinuousLinearMap

@[simp] theorem pairDistributionInftyCLM_apply (s : ℝ)
    (u : WeightedCoeffPairInfty (Weight.sobolev s)) :
    pairDistributionInftyCLM s u =
      (sobolevDistributionSynthesisCLM s (WeightedCoeff.reflection s u.1),
        sobolevDistributionSynthesisCLM s u.2) := rfl

/-- A scalar coefficient test sees the reflected first signed coefficient. -/
@[simp] theorem pairDistributionInfty_fst_coefficientTest (s : ℝ)
    (u : WeightedCoeffPairInfty (Weight.sobolev s)) (n : ℤ) :
    (pairDistributionInftyCLM s u).1 (coefficientTest n) = u.1.val (-n) := by
  simp only [pairDistributionInftyCLM_apply, sobolevDistributionSynthesisCLM_coefficientTest,
    WeightedCoeff.reflection_apply]

@[simp] theorem pairDistributionInfty_snd_coefficientTest (s : ℝ)
    (u : WeightedCoeffPairInfty (Weight.sobolev s)) (n : ℤ) :
    (pairDistributionInftyCLM s u).2 (coefficientTest n) = u.2.val n := by
  simp only [pairDistributionInftyCLM_apply, sobolevDistributionSynthesisCLM_coefficientTest]

/-- Both actual components have period two. -/
theorem pairDistributionInfty_periodic (s : ℝ)
    (u : WeightedCoeffPairInfty (Weight.sobolev s)) :
    IsPeriodTwoDistribution (pairDistributionInftyCLM s u).1 ∧
      IsPeriodTwoDistribution (pairDistributionInftyCLM s u).2 :=
  ⟨isPeriodTwoDistribution_weightedDistributionSynthesis _ _ _,
    isPeriodTwoDistribution_weightedDistributionSynthesis _ _ _⟩

/-- Actual distribution pairs determine all signed raw coefficients. -/
theorem pairDistributionInfty_injective (s : ℝ) :
    Function.Injective (pairDistributionInftyCLM s) := by
  intro u v h
  apply Prod.ext
  · apply Subtype.ext
    funext n
    have hc := congrArg (fun T : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) => T.1 (coefficientTest (-n))) h
    simpa only [pairDistributionInfty_fst_coefficientTest, neg_neg] using hc
  · apply Subtype.ext
    funext n
    have hc := congrArg (fun T : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ) => T.2 (coefficientTest n)) h
    simpa only [pairDistributionInfty_snd_coefficientTest] using hc

/-- The exact source norm, expressed entirely by actual distributional Fourier coefficients. -/
theorem pairDistributionInfty_norm_eq_ciSup (s : ℝ)
    (u : WeightedCoeffPairInfty (Weight.sobolev s)) :
    ‖u‖ = ⨆ n : ℤ, (1 + |(n : ℝ)|) ^ s *
      (‖(pairDistributionInftyCLM s u).1 (coefficientTest (-n))‖ +
        ‖(pairDistributionInftyCLM s u).2 (coefficientTest n)‖) := by
  simp only [pairDistributionInfty_fst_coefficientTest, pairDistributionInfty_snd_coefficientTest,
    neg_neg]
  exact WeightedCoeffPairInfty.sobolev_norm_eq_ciSup s u

/-- Every pair of periodic distributions in the endpoint Sobolev class has a unique
representative carrying the dissertation's frequencywise sum norm. -/
theorem periodicDistribution_pair_infty_iff_existsUnique (s : ℝ)
    (T : 𝓢'(ℝ, ℂ) × 𝓢'(ℝ, ℂ)) :
    ((IsPeriodTwoDistribution T.1 ∧
        Memℓp (fun n : ℤ => (Weight.sobolev s n : ℂ) * T.1 (coefficientTest n)) ⊤) ∧
      (IsPeriodTwoDistribution T.2 ∧
        Memℓp (fun n : ℤ => (Weight.sobolev s n : ℂ) * T.2 (coefficientTest n)) ⊤)) ↔
    ∃! u : WeightedCoeffPairInfty (Weight.sobolev s), pairDistributionInftyCLM s u = T := by
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨a, ha, _⟩ := (periodicDistribution_sobolev_memlp_iff_existsUnique s T.1).mp h₁
    obtain ⟨b, hb, _⟩ := (periodicDistribution_sobolev_memlp_iff_existsUnique s T.2).mp h₂
    let u := (WeightedCoeffPairInfty.toScalarMax s).symm (a, b)
    have hu : pairDistributionInftyCLM s u = T := by
      change ((sobolevDistributionSynthesisCLM s).prodMap (sobolevDistributionSynthesisCLM s))
        ((WeightedCoeffPairInfty.toScalarMax s) u) = T
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact Prod.ext ha hb
    exact ⟨u, hu, fun v hv => pairDistributionInfty_injective s (hv.trans hu.symm)⟩
  · rintro ⟨u, rfl, _⟩
    constructor
    · exact (periodicDistribution_sobolev_memlp_iff_existsUnique s _).mpr
        ⟨WeightedCoeff.reflection s u.1, rfl,
          fun a ha => weightedDistributionSynthesis_injective _ _ ha⟩
    · exact (periodicDistribution_sobolev_memlp_iff_existsUnique s _).mpr
        ⟨u.2, rfl, fun a ha => weightedDistributionSynthesis_injective _ _ ha⟩

end NLS.Fourier
