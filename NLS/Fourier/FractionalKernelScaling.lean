import NLS.Fourier.FractionalKernel

/-!
# Exact frequency scaling of the fractional kernel

Changing variables in the physical displacement integral gives the factor
`n^(2s)` and the model-kernel integral over `[-n,n]`. Integrability is proved
before converting the nonnegative energy to an ordinary real integral.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

def fractionalFrequencyKernel (s : ℝ) (n : ℤ) (x : ℝ) : ℝ :=
  ‖wave n x - 1‖ ^ 2 * |x| ^ (-(1 + 2 * s))

theorem fractionalFrequencyKernel_nonneg (s : ℝ) (n : ℤ) (x : ℝ) :
    0 ≤ fractionalFrequencyKernel s n x :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)

/-- Real and extended-nonnegative kernels agree, also at the removable zero-phase point. -/
theorem fractionalFrequencyKernel_ofReal (s : ℝ) (n : ℤ) (x : ℝ) :
    fractionalTranslationKernel s x * ENNReal.ofReal (‖wave n x - 1‖ ^ 2) =
      ENNReal.ofReal (fractionalFrequencyKernel s n x) := by
  by_cases hx : x = 0
  · subst x
    simp [fractionalFrequencyKernel]
  · rw [fractionalTranslationKernel, ENNReal.ofReal_rpow_of_pos (abs_pos.mpr hx),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
    congr 1
    unfold fractionalFrequencyKernel
    ring

/-- Scaling the phase produces the model kernel and the Jacobian power before integration. -/
theorem fractionalFrequencyKernel_scale (s : ℝ) {n : ℤ} (hn : 0 < n) (x : ℝ) :
    fractionalFrequencyKernel s n x = (n : ℝ) ^ (1 + 2 * s) *
      fractionalModelKernel s ((n : ℝ) * x) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : wave n x = wave 1 ((n : ℝ) * x) := by
    unfold wave
    congr 1
    push_cast
    ring
  have hp : (n : ℝ) ^ (1 + 2 * s) * (n : ℝ) ^ (-(1 + 2 * s)) = 1 := by
    rw [← Real.rpow_add hn']
    simp
  rw [fractionalFrequencyKernel, hw, fractionalModelKernel, abs_mul, abs_of_pos hn',
    Real.mul_rpow hn'.le (abs_nonneg x)]
  calc
    _ = ((n : ℝ) ^ (1 + 2 * s) * (n : ℝ) ^ (-(1 + 2 * s))) *
        (‖wave 1 ((n : ℝ) * x) - 1‖ ^ 2 * |x| ^ (-(1 + 2 * s))) := by rw [hp, one_mul]
    _ = _ := by ring

/-- Every positive-frequency real kernel is integrable in the fractional range. -/
theorem integrable_fractionalFrequencyKernel {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    {n : ℤ} (hn : 0 < n) : Integrable (fractionalFrequencyKernel s n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : fractionalFrequencyKernel s n = fun x => (n : ℝ) ^ (1 + 2 * s) *
      fractionalModelKernel s ((n : ℝ) * x) := funext (fractionalFrequencyKernel_scale s hn)
  rw [he]
  exact ((integrable_fractionalModelKernel hs hs₁).comp_mul_left' hn').const_mul _

/-- Exact change of variables in the physical fractional spectral weight. -/
theorem fractionalSpectralWeight_scale {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    {n : ℤ} (hn : 0 < n) :
    fractionalSpectralWeight s n = ENNReal.ofReal ((n : ℝ) ^ (2 * s) *
      ∫ x in -(n : ℝ)..(n : ℝ), fractionalModelKernel s x) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold fractionalSpectralWeight translationSpectralWeight
  simp_rw [fractionalFrequencyKernel_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_fractionalFrequencyKernel hs hs₁ hn).integrableOn
    (Filter.Eventually.of_forall (fractionalFrequencyKernel_nonneg s n)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  simp_rw [fractionalFrequencyKernel_scale s hn]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ hn'.ne']
  simp only [mul_neg, mul_one, smul_eq_mul]
  congr 1
  have hp : (n : ℝ) ^ (1 + 2 * s) * (n : ℝ)⁻¹ = (n : ℝ) ^ (2 * s) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hn']
    congr 1
    ring
  rw [← mul_assoc, hp]

end NLS.Fourier
