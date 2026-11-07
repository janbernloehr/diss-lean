import NLS.Fourier.UnitIntervalWeakDerivative

/-! # Scalar linearity of actual unit-interval Fourier integrals -/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.Fourier

theorem unitFourierCoefficient_const_mul (f : ℝ → ℂ) (c : ℂ) (n : ℤ) :
    unitFourierCoefficient (fun x => c*f x) n = c*unitFourierCoefficient f n := by
  unfold unitFourierCoefficient
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext x
  ring

theorem unitFourierCoefficient_sub (f g : ℝ → ℂ)
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1) (n : ℤ) :
    unitFourierCoefficient (fun x => f x-g x) n =
      unitFourierCoefficient f n-unitFourierCoefficient g n := by
  unfold unitFourierCoefficient
  simp only [sub_mul]
  exact intervalIntegral.integral_sub
    (hf.mul_continuousOn (continuous_wave _).continuousOn)
    (hg.mul_continuousOn (continuous_wave _).continuousOn)

end NLS.Fourier
