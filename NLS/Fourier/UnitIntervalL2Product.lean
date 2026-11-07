import NLS.Fourier.UnitIntervalWeakDerivative
import NLS.Fourier.IntervalL2BoundedMultiplier

/-! # The full L2 by L2 product in unit-interval Fourier coordinates

The physical product is only assumed integrable. Bilinear Parseval reads its
actual Fourier coefficients as the absolutely convergent discrete convolution.
No Wiener or H1 premise is imposed on either factor.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- Wave multiplication preserves square integrability of arbitrary interval L2 data. -/
theorem memLp_unitInterval_mul_wave (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    MemLp (fun x => f x*wave n x) 2 (volume.restrict (Ioc 0 1)) := by
  simpa only [mul_comm] using memLp_unitInterval_bounded_mul f (wave n) hf
    (continuous_wave n) 1 (by intro x _; simp [wave, Complex.norm_exp])

/-- Modulation shifts each exact unit Fourier integral, including signed frequencies. -/
theorem unitFourierCoefficient_mul_even_wave (f : ℝ → ℂ) (n k : ℤ) :
    unitFourierCoefficient (fun x => f x*wave (-(2*n)) x) k =
      unitFourierCoefficient f (k+n) := by
  unfold unitFourierCoefficient
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [mul_assoc, ← wave_add]
  congr 2
  ring

/-- Hilbert factors have an integrable product with every coefficient given
by the full absolutely convergent convolution of their original unit coefficients. -/
theorem hasSum_unitFourierCoefficient_L2_product (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    HasSum (fun k : ℤ => unitFourierCoefficient f (n-k)*unitFourierCoefficient g k)
      (unitFourierCoefficient (fun x => f x*g x) n) := by
  have h := hasSum_bilinear_unitFourierCoefficient_of_memLp
    (memLp_unitInterval_mul_wave f hf (-(2*n))) hg
  simp only [unitFourierCoefficient_mul_even_wave] at h
  have hs : (fun k : ℤ => unitFourierCoefficient f (-k+n)*unitFourierCoefficient g k) =
      fun k : ℤ => unitFourierCoefficient f (n-k)*unitFourierCoefficient g k := by
    funext k
    rw [show -k+n = n-k by ring]
  rw [hs] at h
  convert h using 1
  unfold unitFourierCoefficient
  apply intervalIntegral.integral_congr
  intro x _
  ring

theorem unitFourierCoefficient_L2_product (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    unitFourierCoefficient (fun x => f x*g x) n =
      ∑' k : ℤ, unitFourierCoefficient f (n-k)*unitFourierCoefficient g k :=
  (hasSum_unitFourierCoefficient_L2_product f g hf hg n).tsum_eq.symm

end NLS.Fourier
