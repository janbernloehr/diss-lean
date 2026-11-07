import NLS.Poisson.GardnerBivector
import NLS.Fourier.UnitIntervalSobolevRealization
import NLS.Fourier.IntervalBilinearParseval

/-! The coefficient Gardner pairing is EXACTLY the printed physical
unit-interval integral for arbitrary H1 cotangents, with their actual
Sobolev representatives and almost-everywhere classical derivatives. -/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.Poisson
open NLS.Fourier

theorem intervalIntegrable_gardner_product (a b : WeightedCoeff (Weight.sobolev 1) 2) :
    IntervalIntegrable (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))*
      deriv (fun t : ℝ => periodOneSobolevSynthesis b (t : AddCircle (2:ℝ))) x) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
  exact (memLp_two_interval (continuous_periodOneSobolevSynthesis a) 0 1 (by norm_num)).integrable_mul
    (memLp_deriv_periodOneSobolevSynthesis b)

theorem gardnerBivector_eq_physical_integral (a b : WeightedCoeff (Weight.sobolev 1) 2) :
    gardnerBivector a b=∫ x in (0:ℝ)..1,
      periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))*
        deriv (fun t : ℝ => periodOneSobolevSynthesis b (t : AddCircle (2:ℝ))) x := by
  have ha (k : ℤ) : unitFourierCoefficient
      (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))) k=a.val k := by
    rw [unitFourierCoefficient_eq_fourierCoeffOn]
    exact periodOneCoefficient_periodOneSobolevSynthesis a k
  have hb (k : ℤ) : unitFourierCoefficient
      (deriv (fun x : ℝ => periodOneSobolevSynthesis b (x : AddCircle (2:ℝ)))) k=
        2*I*(Real.pi:ℂ)*k*b.val k := by
    rw [unitFourierCoefficient_eq_fourierCoeffOn]
    change periodOneCoefficient (deriv (fun x : ℝ => periodOneSobolevSynthesis b
      (x : AddCircle (2:ℝ)))) k=_
    exact periodOneCoefficient_deriv_periodOneSobolevSynthesis b k
  have he := tsum_bilinear_unitFourierCoefficient_of_memLp
    (memLp_two_interval (continuous_periodOneSobolevSynthesis a) 0 1 (by norm_num))
    (memLp_deriv_periodOneSobolevSynthesis b)
  simp only [ha,hb] at he
  rw [gardnerBivector_eq_tsum,← he,
    ← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => a.val (-k)*(2*I*(Real.pi:ℂ)*k*b.val k))]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply,neg_neg,Int.cast_neg]
  ring

end NLS.Poisson
