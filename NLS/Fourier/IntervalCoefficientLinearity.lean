import NLS.Fourier.IntervalCoefficientScaling

/-! # Linearity and interval-local dependence of actual Fourier integrals -/

noncomputable section
open Set MeasureTheory
namespace NLS.Fourier

/-- Coefficients depend only on the function on the integration interval. -/
theorem intervalFourierCoefficient_congr (T : ℝ) (f g : ℝ → ℂ)
    (h : EqOn f g (uIcc 0 T)) (n : ℤ) :
    intervalFourierCoefficient T f n = intervalFourierCoefficient T g n := by
  unfold intervalFourierCoefficient
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [h ht]

/-- Continuous interval data have additive actual Fourier coefficients. -/
theorem intervalFourierCoefficient_add (T : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    intervalFourierCoefficient T (fun t => f t+g t) n =
      intervalFourierCoefficient T f n+intervalFourierCoefficient T g n := by
  have hw : Continuous (fun t : ℝ => wave (-n) ((2/T)*t)) :=
    (continuous_wave _).comp (continuous_const.mul continuous_id)
  have hiF : IntervalIntegrable (fun t => f t*wave (-n) ((2/T)*t)) volume 0 T :=
    (hf.mul hw).intervalIntegrable 0 T
  have hiG : IntervalIntegrable (fun t => g t*wave (-n) ((2/T)*t)) volume 0 T :=
    (hg.mul hw).intervalIntegrable 0 T
  unfold intervalFourierCoefficient
  simp only [add_mul]
  rw [intervalIntegral.integral_add hiF hiG,mul_add]

end NLS.Fourier
