import NLS.Fourier.IntervalContinuousUniqueness
import NLS.Fourier.IntervalParseval

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.Fourier



/-- A fixed parity of half coefficients is precisely the native unit Fourier
sequence of the corresponding modulated function, with the factor two retained. -/
theorem unitFourierCoefficient_eq_two_halfCoefficient_parity
    (f : ℝ → ℂ) (r k : ℤ) :
    intervalFourierCoefficient 1 (fun x => f x*wave (-r) x) k =
      2*halfCoefficient f (2*k+r) := by
  rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),fourierCoeffOn_one]
  congr 1
  unfold halfCoefficient
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [mul_assoc,← wave_add]
  congr 2
  ring

/-- Each parity separately determines a continuous function on the original
unit interval. No endpoint matching or periodicity of the input is assumed. -/
theorem eq_zero_on_unitInterval_of_halfCoefficient_parity_zero
    (f : ℝ → ℂ) (hf : Continuous f) (r : ℤ)
    (hzero : ∀ k : ℤ, halfCoefficient f (2*k+r)=0) :
    EqOn f (fun _ => 0) (Icc (0 : ℝ) 1) := by
  have hh := eqOn_Icc_of_intervalFourierCoefficient_eq (L := 1) (by norm_num)
    (fun x => f x*wave (-r) x) (fun _ => 0) (hf.mul (continuous_wave (-r))) continuous_const (by
      intro k
      rw [unitFourierCoefficient_eq_two_halfCoefficient_parity,hzero]
      simp [intervalFourierCoefficient])
  intro x hx
  have hm := hh hx
  exact (mul_eq_zero.mp hm).resolve_right (Complex.exp_ne_zero _)

end NLS.Fourier
