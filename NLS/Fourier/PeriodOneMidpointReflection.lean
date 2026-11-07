import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra

/-! Literal midpoint reflection reverses every physical Fourier index. -/
noncomputable section
open Complex MeasureTheory
namespace NLS.Fourier

theorem periodOneCoefficient_midpointReflection (f : ℝ → ℂ) (n : ℤ) :
    periodOneCoefficient (fun x => f (1-x)) n = periodOneCoefficient f (-n) := by
  have hw (x : ℝ) : wave (-(2*(-n))) (1-x) = wave (-(2*n)) x := by
    simp only [mul_neg,neg_neg]
    rw [sub_eq_add_neg,wave_add_argument,wave_even_at_one,one_mul]
    unfold wave
    congr 1
    push_cast
    ring
  have he : (fun x : ℝ => f (1-x)*wave (-(2*n)) x) =
      (fun x : ℝ => (fun y => f y*wave (-(2*(-n))) y) (1-x)) := by
    funext x
    change f (1-x)*wave (-(2*n)) x = f (1-x)*wave (-(2*(-n))) (1-x)
    rw [hw]
  rw [periodOneCoefficient,periodOneCoefficient,
    ← unitFourierCoefficient_eq_fourierCoeffOn,← unitFourierCoefficient_eq_fourierCoeffOn]
  unfold unitFourierCoefficient
  rw [he]
  simpa only [sub_self,sub_zero] using
    (intervalIntegral.integral_comp_sub_left (fun y => f y*wave (-(2*(-n))) y)
      (a := (0:ℝ)) (b := 1) 1)

end NLS.Fourier
