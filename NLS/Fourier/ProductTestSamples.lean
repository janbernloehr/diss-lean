import NLS.Fourier.DistributionModulation
import NLS.SequenceSpaces.TestConvolution

/-!
# Actual test integrals for continuous Fourier multipliers

Multiplying a Schwartz test by an absolutely convergent periodic Fourier series
need not give a Schwartz function. Its signed Fourier samples are nevertheless
absolutely summable. This supplies a canonical extended action for the Fourier
class, expressed through actual real-line integrals.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier

/-- The summable Fourier test sequence after multiplication by a continuous Fourier series. -/
def productTestSamples (b : Coeff 1) (g : 𝓢(ℝ, ℂ)) : Coeff 1 :=
  Coeff.convolution (schwartzSamples (𝓕 g)) (Coeff.reflection b)

@[simp] theorem productTestSamples_apply (b : Coeff 1) (g : 𝓢(ℝ, ℂ)) (n : ℤ) :
    productTestSamples b g n = ∑' k : ℤ, b k * (𝓕 g) (-((n + k : ℤ) : ℝ) / 2) :=
  Coeff.convolution_reflection_apply b (schwartzSamples (𝓕 g)) n

/-- The test coefficients are actual Fourier integrals of the multiplied test. -/
theorem productTestSamples_eq_integral (b : Coeff 1) (g : 𝓢(ℝ, ℂ)) (n : ℤ) :
    productTestSamples b g n =
      ∫ x : ℝ, wave n x * (continuousSynthesis b (x : AddCircle (2 : ℝ)) * g x) := by
  have hw (m : ℤ) (x : ℝ) : ‖wave m x‖ = 1 := by simp [wave, Complex.norm_exp]
  have hi (k : ℤ) : Integrable (fun x : ℝ => (b k * wave (n+k) x) * g x) := by
    apply (g.integrable.norm.const_mul ‖b k‖).mono'
      (((continuous_const.mul (continuous_wave (n+k))).mul g.continuous).aestronglyMeasurable)
    filter_upwards [] with x
    simp [hw]
  have hs : Summable (fun k : ℤ => ∫ x : ℝ, ‖(b k * wave (n+k) x) * g x‖) := by
    simp only [norm_mul, hw, mul_one, integral_const_mul]
    exact (lp.memℓp b).norm.summable_of_one.mul_right _
  calc
    _ = ∑' k : ℤ, ∫ x : ℝ, (b k * wave (n+k) x) * g x := by
      rw [productTestSamples_apply]
      apply tsum_congr
      intro k
      rw [fourier_sample_eq_integral_wave, ← integral_const_mul]
      congr 1
      funext x
      ring
    _ = ∫ x : ℝ, ∑' k : ℤ, (b k * wave (n+k) x) * g x :=
      integral_tsum_of_summable_integral_norm hi hs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [continuousSynthesis_apply, ← tsum_mul_right, ← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [wave_add]
      ring

/-- The actual Fourier integrals of the multiplied test are absolutely summable. -/
theorem summable_norm_productTest_integrals (b : Coeff 1) (g : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖∫ x : ℝ,
      wave n x * (continuousSynthesis b (x : AddCircle (2 : ℝ)) * g x)‖) := by
  simp_rw [← productTestSamples_eq_integral]
  exact (lp.memℓp (productTestSamples b g)).norm.summable_of_one

/-- Uniform control of the enlarged test sequence by its multiplier coefficients. -/
theorem norm_productTestSamples_le (b : Coeff 1) (g : 𝓢(ℝ, ℂ)) :
    ‖productTestSamples b g‖ ≤ ‖b‖ * ‖schwartzSamples (𝓕 g)‖ := by
  have h := Coeff.norm_convolution_le (schwartzSamples (𝓕 g)) (Coeff.reflection b)
  rw [Coeff.reflection.norm_map] at h
  simpa only [productTestSamples, mul_comm] using h

/-- When the multiplier is smooth, the enlarged test is the genuine multiplied Schwartz test. -/
theorem productTestSamples_eq_smooth_samples (b : Coeff 1)
    (hb : (fun x : ℝ => continuousSynthesis b (x : AddCircle (2 : ℝ))).HasTemperateGrowth)
    (g : 𝓢(ℝ, ℂ)) :
    productTestSamples b g = schwartzSamples (𝓕 (SchwartzMap.smulLeftCLM ℂ
      (fun x : ℝ => continuousSynthesis b (x : AddCircle (2 : ℝ))) g)) := by
  ext n
  rw [productTestSamples_eq_integral, schwartzSamples_apply, fourier_sample_eq_integral_wave]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [SchwartzMap.smulLeftCLM_apply_apply hb, smul_eq_mul]

/-- A continuous Fourier multiplier times a Schwartz test is integrable on the real line. -/
theorem integrable_synthesis_mul_test (b : Coeff 1) (g : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => continuousSynthesis b (x : AddCircle (2 : ℝ)) * g x) := by
  apply (g.integrable.norm.const_mul ‖b‖).mono'
    (((continuousSynthesis b).continuous.comp (by fun_prop)).mul g.continuous).aestronglyMeasurable
  filter_upwards [] with x
  change ‖continuousSynthesis b (x : AddCircle (2 : ℝ)) * g x‖ ≤ ‖b‖ * ‖g x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (((continuousSynthesis b).norm_coe_le_norm _).trans (norm_continuousSynthesis_le b))
    (norm_nonneg _)

/-- An absolutely convergent periodic series may be integrated against any integrable function. -/
theorem tsum_integral_wave_eq_integral_synthesis (a : Coeff 1) (u : ℝ → ℂ) (hu : Integrable u) :
    (∑' n : ℤ, a n * ∫ x : ℝ, wave n x * u x) =
      ∫ x : ℝ, continuousSynthesis a (x : AddCircle (2 : ℝ)) * u x := by
  have hw (n : ℤ) (x : ℝ) : ‖wave n x‖ = 1 := by simp [wave, Complex.norm_exp]
  have hi (n : ℤ) : Integrable (fun x : ℝ => (a n * wave n x) * u x) := by
    apply (hu.norm.const_mul ‖a n‖).mono'
      (((continuous_const.mul (continuous_wave n)).aestronglyMeasurable).mul hu.aestronglyMeasurable)
    filter_upwards [] with x
    simp [hw]
  have hs : Summable (fun n : ℤ => ∫ x : ℝ, ‖(a n * wave n x) * u x‖) := by
    simp only [norm_mul, hw, mul_one, integral_const_mul]
    exact (lp.memℓp a).norm.summable_of_one.mul_right _
  calc
    _ = ∑' n : ℤ, ∫ x : ℝ, (a n * wave n x) * u x := by
      apply tsum_congr
      intro n
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    _ = ∫ x : ℝ, ∑' n : ℤ, (a n * wave n x) * u x :=
      integral_tsum_of_summable_integral_norm hi hs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [continuousSynthesis_apply, tsum_mul_right]

end NLS.Fourier
