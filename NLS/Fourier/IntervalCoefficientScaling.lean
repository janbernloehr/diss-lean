import NLS.Fourier.IntervalDilation
import NLS.Fourier.IntervalParseval

/-!
# Actual Fourier coefficients on an arbitrary positive period

The coefficient is the normalized physical integral with frequency `2πn/L`.
It agrees with mathlib's interval coefficient and with the period-two
coefficient after the physical dilation `x ↦ (L/2)x`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Normalized physical Fourier integral on an interval of length `L`. -/
def intervalFourierCoefficient (L : ℝ) (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  ((1 / L : ℝ) : ℂ) * ∫ x in (0 : ℝ)..L, f x * wave (-n) ((2 / L) * x)

/-- The arbitrary-period integral is mathlib's actual interval Fourier coefficient. -/
theorem intervalFourierCoefficient_eq_fourierCoeffOn {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) (n : ℤ) :
    intervalFourierCoefficient L f n = fourierCoeffOn hL f n := by
  rw [fourierCoeffOn_eq_integral]
  simp only [fourier_coe_apply, sub_zero, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one]
  unfold intervalFourierCoefficient
  push_cast
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  have he : Complex.exp (2 * Real.pi * Complex.I * (-n : ℤ) * x / L) = wave (-n) ((2 / L) * x) := by
    unfold wave
    push_cast
    congr 1
    ring
  push_cast at he
  dsimp only
  rw [he]
  ring

@[simp] theorem intervalFourierCoefficient_two (f : ℝ → ℂ) (n : ℤ) :
    intervalFourierCoefficient 2 f n = periodTwoCoefficient f n := by
  simp [intervalFourierCoefficient, periodTwoCoefficient]

/-- Positive physical dilation gives exactly the same normalized Fourier coefficients. -/
theorem periodTwoCoefficient_intervalDilation {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) (n : ℤ) :
    periodTwoCoefficient (intervalDilation (L / 2) f) n = intervalFourierCoefficient L f n := by
  have hc : 0 < L / 2 := by positivity
  let G := fun x : ℝ => f x * wave (-n) ((2 / L) * x)
  have he : (fun x : ℝ => intervalDilation (L / 2) f x * wave (-n) x) =
      fun x => G ((L / 2) * x) := by
    funext x
    dsimp only [intervalDilation, G]
    congr 2
    field_simp
  rw [periodTwoCoefficient, he, intervalIntegral.integral_comp_mul_left G hc.ne']
  simp only [mul_zero, div_mul_cancel₀ L (by norm_num : (2 : ℝ) ≠ 0), Complex.real_smul]
  unfold intervalFourierCoefficient
  rw [← mul_assoc]
  change (1 / 2 : ℂ) * (((L / 2 : ℝ)⁻¹ : ℝ) : ℂ) * (∫ x in (0 : ℝ)..L, G x) = _
  congr 1
  push_cast
  field_simp

/-- Equality of the full coefficient functions, useful for sequence-space membership. -/
theorem periodTwoCoefficient_intervalDilation_eq {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) :
    periodTwoCoefficient (intervalDilation (L / 2) f) = intervalFourierCoefficient L f :=
  funext (periodTwoCoefficient_intervalDilation hL f)

/-- Square-integrable arbitrary-period data becomes period-two square-integrable data. -/
theorem memLp_periodTwoDilation {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 L))) :
    MemLp (intervalDilation (L / 2) f) 2 (volume.restrict (Ioc 0 2)) := by
  apply memLp_intervalDilation_Ioc (by positivity) 2 f
  simpa only [div_mul_cancel₀ L (by norm_num : (2 : ℝ) ≠ 0)] using hf

end NLS.Fourier
