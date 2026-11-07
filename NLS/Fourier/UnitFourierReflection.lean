import NLS.Fourier.UnitIntervalFourierLinear
import NLS.Fourier.PeriodOneCoefficients

/-! # Unit-interval Fourier integrals under midpoint reflection -/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.Fourier

theorem wave_even_one_sub (k : ℤ) (x : ℝ) : wave (2*k) (1-x) = wave (-(2*k)) x := by
  calc
    _ = wave (2*k) (2-(x+1)) := by congr 1; ring
    _ = wave (-(2*k)) (x+1) := wave_reflect _ _
    _ = wave (-(2*k)) x*wave (-(2*k)) 1 := wave_add_argument _ _ _
    _ = _ := by rw [show -(2*k) = 2*(-k) by ring,wave_even_at_one,mul_one]

theorem unitFourierCoefficient_one_sub (f : ℝ → ℂ) (k : ℤ) :
    unitFourierCoefficient (fun x => f (1-x)) k = unitFourierCoefficient f (-k) := by
  unfold unitFourierCoefficient
  have he : (fun x : ℝ => f (1-x)*wave (-(2*k)) x) =
      (fun x : ℝ => (fun y : ℝ => f y*wave (-(2*(-k))) y) (1-x)) := by
    funext x
    dsimp only
    rw [show -(2*(-k)) = 2*k by ring,wave_even_one_sub]
  rw [he]
  simpa only [sub_self,sub_zero] using
    intervalIntegral.integral_comp_sub_left (fun y : ℝ => f y*wave (-(2*(-k))) y)
      (1:ℝ) (a := 0) (b := 1)

end NLS.Fourier
