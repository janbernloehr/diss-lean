import NLS.Poisson.SourceCoordinateBrackets
import NLS.Fourier.IntervalBilinearParseval
import NLS.Fourier.PeriodOneCoefficients

/-! # The native complex bilinear Hilbert pairing is the actual unit integral

Both L² inputs use their original unit-period Fourier integrals. The
reversed frequency is retained explicitly; no conjugate-linear pairing
or period-two scale factor is introduced.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ENNReal
namespace NLS.Poisson

theorem reflectedHilbertPairing_eq_unit_integral (a b : Coeff 2) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (ha : ∀ n, a n = periodOneCoefficient f n) (hb : ∀ n, b n = periodOneCoefficient g n) :
    reflectedHilbertPairing a b = ∫ x in (0 : ℝ)..1,f x*g x := by
  rw [reflectedHilbertPairing_apply]
  have he : (∑' n : ℤ,a n*b (-n)) = ∑' n : ℤ,a (-n)*b n := by
    simpa only [Equiv.neg_apply,neg_neg] using (Equiv.neg ℤ).tsum_eq (fun n : ℤ => a (-n)*b n)
  rw [he]
  have hc (h : ℝ → ℂ) (n : ℤ) : periodOneCoefficient h n = unitFourierCoefficient h n :=
    (unitFourierCoefficient_eq_fourierCoeffOn h n).symm
  simpa only [ha,hb,hc] using tsum_bilinear_unitFourierCoefficient_of_memLp hf hg

end NLS.Poisson
