import NLS.Fourier.DistributionSynthesis
import NLS.Fourier.PeriodOneCoefficients

/-!
# Physical periodicity of distributional Fourier synthesis

Translations of Schwartz tests show that the synthesized tempered distribution
has period two, and that the doubled period-one coefficients have period one.
For absolutely summable data the distribution agrees with the existing actual
continuous Fourier series under integration over the real line.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translation of a test gives the period-two Fourier phase. -/
theorem fourier_sample_translate (g : 𝓢(ℝ, ℂ)) (n : ℤ) (t : ℝ) :
    (𝓕 (SchwartzMap.compSubConstCLM ℂ t g)) (-(n : ℝ) / 2) =
      wave n t * (𝓕 g) (-(n : ℝ) / 2) := by
  rw [fourier_sample_eq_integral_wave, fourier_sample_eq_integral_wave]
  change (∫ x : ℝ, wave n x * g (x - t)) = _
  calc
    _ = ∫ x : ℝ, wave n (x + t) * g x := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (fun x : ℝ => wave n x * g (x - t)) t).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [wave_add_argument]
      ring

/-- A phase-invariant coefficient sequence yields a translation-invariant distribution. -/
theorem distributionSynthesis_translate_of_phase (a : Coeff p) (t : ℝ)
    (hphase : ∀ n : ℤ, a n * wave n t = a n) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis a (SchwartzMap.compSubConstCLM ℂ t g) =
      distributionSynthesis a g := by
  simp only [distributionSynthesis_apply, fourier_sample_translate]
  apply tsum_congr
  intro n
  rw [← mul_assoc, hphase]

/-- Every synthesized distribution has physical period two. -/
theorem distributionSynthesis_period_two (a : Coeff p) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis a (SchwartzMap.compSubConstCLM ℂ 2 g) =
      distributionSynthesis a g := by
  apply distributionSynthesis_translate_of_phase
  intro n
  have hw : wave n 2 = 1 := by
    convert wave_even_at_one n using 1
    unfold wave
    congr 1
    push_cast
    ring
  rw [hw, mul_one]

/-- Evenly supported coefficients define period-one distributions. -/
theorem distributionSynthesis_period_one_of_even (a : Coeff p)
    (ha : a ∈ Coeff.paritySubspace (p := p) 0) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis a (SchwartzMap.compSubConstCLM ℂ 1 g) =
      distributionSynthesis a g := by
  apply distributionSynthesis_translate_of_phase
  intro n
  by_cases hn : n % 2 = 0
  · have he : n = 2 * (n / 2) := by omega
    rw [he, wave_even_at_one, mul_one]
  · rw [(Coeff.mem_paritySubspace 0 a).mp ha n (by simpa using hn), zero_mul]

/-- The earlier coefficient doubling now gives an actual period-one distribution. -/
theorem distributionSynthesis_periodDouble_period_one (a : Coeff p) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (Coeff.periodDouble a) (SchwartzMap.compSubConstCLM ℂ 1 g) =
      distributionSynthesis (Coeff.periodDouble a) g :=
  distributionSynthesis_period_one_of_even _ (Coeff.periodDouble_mem a) g

/-- Translation can also be detected separately at each frequency. -/
theorem distributionSynthesis_translate_coefficientTest (a : Coeff p) (t : ℝ) (n : ℤ) :
    distributionSynthesis a (SchwartzMap.compSubConstCLM ℂ t (coefficientTest n)) =
      a n * wave n t := by
  classical
  simp only [distributionSynthesis_apply, fourier_sample_translate, coefficientTest,
    FourierTransform.fourier_fourierInv_eq, frequencyTest_sample]
  simp

/-- Period one is equivalent to vanishing of all odd Fourier coefficients. -/
theorem distributionSynthesis_period_one_iff (a : Coeff p) :
    (∀ g : 𝓢(ℝ, ℂ), distributionSynthesis a (SchwartzMap.compSubConstCLM ℂ 1 g) =
      distributionSynthesis a g) ↔ a ∈ Coeff.paritySubspace (p := p) 0 := by
  refine ⟨fun h => ?_, fun ha g => distributionSynthesis_period_one_of_even a ha g⟩
  apply (Coeff.mem_paritySubspace 0 a).mpr
  intro n hn
  have he : n = 2 * (n / 2) + 1 := by omega
  have hw : wave n 1 = -1 := by rw [he, wave_odd_at_one]
  have ht := h (coefficientTest n)
  rw [distributionSynthesis_translate_coefficientTest, distributionSynthesis_coefficientTest,
    hw] at ht
  linear_combination -(1 / 2 : ℂ) * ht

/-- For `ℓ¹` coefficients, the new distribution is the actual continuous Fourier series. -/
theorem distributionSynthesis_eq_integral_continuousSynthesis (a : Coeff 1) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis a g =
      ∫ x : ℝ, continuousSynthesis a (x : AddCircle (2 : ℝ)) * g x := by
  have hw (n : ℤ) (x : ℝ) : ‖wave n x‖ = 1 := by simp [wave, Complex.norm_exp]
  have hi (n : ℤ) : Integrable (fun x : ℝ => (a n * wave n x) * g x) := by
    apply (g.integrable.norm.const_mul ‖a n‖).mono'
      (((continuous_const.mul (continuous_wave n)).mul g.continuous).aestronglyMeasurable)
    filter_upwards [] with x
    simp [hw]
  have hs : Summable (fun n : ℤ => ∫ x : ℝ, ‖(a n * wave n x) * g x‖) := by
    simp only [norm_mul, hw, mul_one, integral_const_mul]
    exact (lp.memℓp a).norm.summable_of_one.mul_right _
  calc
    _ = ∑' n : ℤ, ∫ x : ℝ, (a n * wave n x) * g x := by
      rw [distributionSynthesis_apply]
      apply tsum_congr
      intro n
      rw [fourier_sample_eq_integral_wave, ← integral_const_mul]
      congr 1
      funext x
      ring
    _ = ∫ x : ℝ, ∑' n : ℤ, (a n * wave n x) * g x :=
      integral_tsum_of_summable_integral_norm hi hs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [continuousSynthesis_apply, tsum_mul_right]

/-- The unit-period continuous synthesis has the same distribution as doubled coefficients. -/
theorem distributionSynthesis_periodDouble_eq_integral (a : Coeff 1) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (Coeff.periodDouble a) g =
      ∫ x : ℝ, periodOneSynthesis a x * g x :=
  distributionSynthesis_eq_integral_continuousSynthesis (Coeff.periodDouble a) g

end NLS.Fourier
