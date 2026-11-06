import NLS.Fourier.UnitIntervalWeakDerivative

/-! # Exact unit-interval Fourier coefficients of actual L2 products -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter
open scoped ENNReal
namespace NLS.Fourier

theorem unitFourierCoefficient_const_mul (c : ℂ) (f : ℝ → ℂ) (n : ℤ) :
    unitFourierCoefficient (fun x => c*f x) n = c*unitFourierCoefficient f n := by
  unfold unitFourierCoefficient
  simp_rw [mul_assoc]
  exact intervalIntegral.integral_const_mul _ _

/-- The literal L1 product has the original absolutely convergent
convolution coefficients, with no continuity or endpoint hypothesis. -/
theorem unitFourierCoefficient_mul_of_memLp (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    unitFourierCoefficient (fun x => f x*g x) n =
      ∑' k : ℤ, unitFourierCoefficient f (n-k)*unitFourierCoefficient g k := by
  let h : ℝ → ℂ := fun x => f x*wave (-(2*n)) x
  have hh : MemLp h 2 (volume.restrict (Ioc 0 1)) := by
    apply hf.norm.mono' (hf.aestronglyMeasurable.mul (continuous_wave _).aestronglyMeasurable)
    exact Eventually.of_forall (fun x => by simp [wave,Complex.norm_exp])
  have hcoeff (k : ℤ) : unitFourierCoefficient h (-k) = unitFourierCoefficient f (n-k) := by
    unfold unitFourierCoefficient
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [h]
    rw [mul_assoc,←wave_add]
    congr 2
    ring
  have hs := tsum_bilinear_unitFourierCoefficient_of_memLp hh hg
  simp_rw [hcoeff] at hs
  rw [hs]
  apply intervalIntegral.integral_congr
  intro x _
  change (f x*g x)*wave (-(2*n)) x = (f x*wave (-(2*n)) x)*g x
  ring

end NLS.Fourier
