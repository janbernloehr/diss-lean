import NLS.Fourier.DistributionDilation
import NLS.Fourier.WeightedDistributionIdentification

/-! # Fourier identification on every positive period

The period is reduced to two through actual distributional dilation. Normalized
Schwartz coefficient tests and inverse dilation preserve the original object.
-/
noncomputable section
open scoped ENNReal SchwartzMap
namespace NLS.Fourier

/-- Normalized coefficient-extracting Schwartz tests for every positive period. -/
def periodCoefficientTest (L : ℝ) (hL : 0 < L) (n : ℤ) : 𝓢(ℝ, ℂ) :=
  ((L/2 : ℝ) : ℂ)⁻¹ • schwartzDilationCLM (L/2)⁻¹ (inv_ne_zero (by positivity)) (coefficientTest n)

/-- Period two recovers the existing coefficient tests exactly. -/
@[simp] theorem periodCoefficientTest_two (n : ℤ) :
    periodCoefficientTest 2 (by norm_num) n = coefficientTest n := by
  ext x
  simp [periodCoefficientTest,schwartzDilationCLM_apply]

theorem isPeriodTwoDistribution_dilation (L : ℝ) (hL : 0 < L) (T : 𝓢'(ℝ, ℂ))
    (hT : IsPeriodicDistribution L T) :
    IsPeriodTwoDistribution (distributionDilation (L/2) (by positivity) T) := by
  have h := distributionDilation_periodic (L/2) (by positivity) L T hT
  have he : L/(L/2) = 2 := by field_simp
  rw [he] at h
  exact h

theorem distributionDilation_periodCoefficientTest (L : ℝ) (hL : 0 < L) (T : 𝓢'(ℝ, ℂ)) (n : ℤ) :
    distributionDilation (L/2) (by positivity) T (coefficientTest n) = T (periodCoefficientTest L hL n) := by
  rw [distributionDilation_apply,periodCoefficientTest,map_smul]
  rfl

/-- Exact normalized periodization of every coefficient-extracting test. -/
theorem periodCoefficientTest_periodization (L : ℝ) (hL : 0 < L) (n : ℤ) (x : ℝ) :
    (∑' k : ℤ, periodCoefficientTest L hL n (x+L*k)) =
      (L : ℂ)⁻¹*wave (-n) ((L/2)⁻¹*x) := by
  have he (k : ℤ) : (L/2)⁻¹*(x+L*k) = (L/2)⁻¹*x+2*k := by
    field_simp
  simp only [periodCoefficientTest,smul_apply,schwartzDilationCLM_apply,smul_eq_mul,he]
  rw [tsum_mul_left,← periodization_eq_tsum,periodization_coefficientTest]
  simp only [ContinuousMap.smul_apply,smul_eq_mul,fourier_two_eq_wave]
  push_cast
  field_simp

/-- In particular the zero-mode window has constant periodization 1/L. -/
theorem periodCoefficientTest_zero_periodization (L : ℝ) (hL : 0 < L) (x : ℝ) :
    (∑' k : ℤ, periodCoefficientTest L hL 0 (x+L*k)) = (L : ℂ)⁻¹ := by
  simp only [periodCoefficientTest_periodization,neg_zero,wave_zero,mul_one]

/-- Actual periodic distributions are determined by these normalized Fourier coefficients. -/
theorem periodicDistribution_ext_arbitraryPeriod (L : ℝ) (hL : 0 < L)
    {T U : 𝓢'(ℝ, ℂ)} (hT : IsPeriodicDistribution L T) (hU : IsPeriodicDistribution L U)
    (h : ∀ n, T (periodCoefficientTest L hL n) = U (periodCoefficientTest L hL n)) : T = U := by
  apply distributionDilation_injective (L/2) (by positivity)
  apply periodicDistribution_ext (isPeriodTwoDistribution_dilation L hL T hT)
    (isPeriodTwoDistribution_dilation L hL U hU)
  intro n
  rw [distributionDilation_periodCoefficientTest L hL T n,
    distributionDilation_periodCoefficientTest L hL U n,h n]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Weighted coefficient data as an actual distribution of any positive period. -/
def arbitraryPeriodDistributionSynthesis (L : ℝ) (hL : 0 < L) (w : Weight)
    (hw : w.HasTemperedInverse) (a : WeightedCoeff w p) : 𝓢'(ℝ, ℂ) :=
  distributionDilation (L/2)⁻¹ (inv_ne_zero (by positivity)) (weightedDistributionSynthesis w hw a)

/-- Synthesis has the stated physical period. -/
theorem arbitraryPeriodDistributionSynthesis_periodic (L : ℝ) (hL : 0 < L) (w : Weight)
    (hw : w.HasTemperedInverse) (a : WeightedCoeff w p) :
    IsPeriodicDistribution L (arbitraryPeriodDistributionSynthesis L hL w hw a) := by
  have h := distributionDilation_periodic (L/2)⁻¹ (inv_ne_zero (by positivity)) 2
    (weightedDistributionSynthesis w hw a) (isPeriodTwoDistribution_weightedDistributionSynthesis w hw a)
  have he : 2 / (L/2)⁻¹ = L := by field_simp
  rw [he] at h
  exact h

/-- Every raw coefficient is recovered with no period-dependent factor. -/
@[simp] theorem arbitraryPeriodDistributionSynthesis_coefficient (L : ℝ) (hL : 0 < L) (w : Weight)
    (hw : w.HasTemperedInverse) (a : WeightedCoeff w p) (n : ℤ) :
    arbitraryPeriodDistributionSynthesis L hL w hw a (periodCoefficientTest L hL n) = a.val n := by
  rw [← distributionDilation_periodCoefficientTest,arbitraryPeriodDistributionSynthesis,
    distributionDilation_inverse_right,weightedDistributionSynthesis_coefficientTest]

/-- At period two, the new synthesis is the existing weighted distribution. -/
theorem arbitraryPeriodDistributionSynthesis_two (w : Weight) (hw : w.HasTemperedInverse)
    (a : WeightedCoeff w p) :
    arbitraryPeriodDistributionSynthesis 2 (by norm_num) w hw a = weightedDistributionSynthesis w hw a := by
  apply periodicDistribution_ext_arbitraryPeriod 2 (by norm_num)
    (arbitraryPeriodDistributionSynthesis_periodic 2 (by norm_num) w hw a)
    (isPeriodTwoDistribution_weightedDistributionSynthesis w hw a)
  intro n
  rw [arbitraryPeriodDistributionSynthesis_coefficient,periodCoefficientTest_two,
    weightedDistributionSynthesis_coefficientTest]

/-- Synthesis is faithful to the original raw weighted coefficients. -/
theorem arbitraryPeriodDistributionSynthesis_injective (L : ℝ) (hL : 0 < L) (w : Weight)
    (hw : w.HasTemperedInverse) : Function.Injective (arbitraryPeriodDistributionSynthesis (p := p) L hL w hw) := by
  intro a b h
  apply Subtype.ext
  funext n
  simpa only [arbitraryPeriodDistributionSynthesis_coefficient] using
    congrArg (fun T : 𝓢'(ℝ, ℂ) => T (periodCoefficientTest L hL n)) h

/-- The original weighted Fourier-Lebesgue membership characterizes every periodic distribution. -/
theorem periodicDistribution_weighted_memlp_iff_existsUnique_arbitraryPeriod
    (L : ℝ) (hL : 0 < L) (w : Weight) (hw : w.HasTemperedInverse) (T : 𝓢'(ℝ, ℂ)) :
    (IsPeriodicDistribution L T ∧
      Memℓp (fun n : ℤ => (w n : ℂ)*T (periodCoefficientTest L hL n)) p) ↔
      ∃! a : WeightedCoeff w p, arbitraryPeriodDistributionSynthesis L hL w hw a = T := by
  constructor
  · rintro ⟨hT,ha⟩
    let a : WeightedCoeff w p := ⟨fun n => T (periodCoefficientTest L hL n),ha⟩
    have he : arbitraryPeriodDistributionSynthesis L hL w hw a = T := by
      apply periodicDistribution_ext_arbitraryPeriod L hL
        (arbitraryPeriodDistributionSynthesis_periodic L hL w hw a) hT
      intro n
      exact arbitraryPeriodDistributionSynthesis_coefficient L hL w hw a n
    exact ⟨a,he,fun b hb => arbitraryPeriodDistributionSynthesis_injective L hL w hw (hb.trans he.symm)⟩
  · rintro ⟨a,ha,_⟩
    rw [← ha]
    refine ⟨arbitraryPeriodDistributionSynthesis_periodic L hL w hw a,?_⟩
    simp only [arbitraryPeriodDistributionSynthesis_coefficient]
    exact a.property

/-- Continuous linear synthesis in the actual distribution topology for every positive period. -/
def arbitraryPeriodDistributionSynthesisCLM (L : ℝ) (hL : 0 < L) (w : Weight)
    (hw : w.HasTemperedInverse) : WeightedCoeff w p →L[ℂ] 𝓢'(ℝ, ℂ) :=
  (distributionDilationCLM (L/2)⁻¹ (inv_ne_zero (by positivity))).comp
    (weightedDistributionSynthesisCLM w hw)

@[simp] theorem arbitraryPeriodDistributionSynthesisCLM_apply (L : ℝ) (hL : 0 < L) (w : Weight)
    (hw : w.HasTemperedInverse) (a : WeightedCoeff w p) :
    arbitraryPeriodDistributionSynthesisCLM L hL w hw a =
      arbitraryPeriodDistributionSynthesis L hL w hw a := rfl

/-- Distributional convergence of Fourier sums holds on every period, including the infinity endpoint. -/
theorem tendsto_arbitraryPeriodDistributionSynthesis_truncate (L : ℝ) (hL : 0 < L) (w : Weight)
    (hw : w.HasTemperedInverse) (a : WeightedCoeff w p) :
    Filter.Tendsto (fun S : Finset ℤ => arbitraryPeriodDistributionSynthesis L hL w hw
      (WeightedCoeff.truncate w p S a)) Filter.atTop
        (nhds (arbitraryPeriodDistributionSynthesis L hL w hw a)) := by
  exact ((distributionDilationCLM (L/2)⁻¹ (inv_ne_zero (by positivity))).continuous.tendsto
    (weightedDistributionSynthesis w hw a)).comp (tendsto_weightedDistributionSynthesis_truncate w hw a)

end NLS.Fourier
