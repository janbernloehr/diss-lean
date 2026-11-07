import NLS.Poisson.GardnerBivector
import NLS.Fourier.UnitCoefficientPrescribedDerivative

/-! Transfer the ACTUAL Gardner integral using original Fourier
coefficients. No pointwise identification of chosen Sobolev representatives
or extra smoothness assumption on the source potential is required. -/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.Poisson
open NLS.Fourier

theorem gardnerBivector_eq_integral_of_coefficients
    (a b : WeightedCoeff (Weight.sobolev 1) 2) (f g g1 : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hg1 : Continuous g1)
    (hdg : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g (g1 t) t) (hgp : g 1=g 0)
    (ha : ∀ k : ℤ, a.val k=unitFourierCoefficient f k)
    (hb : ∀ k : ℤ, b.val k=unitFourierCoefficient g k) :
    gardnerBivector a b=∫ x in (0:ℝ)..1, f x*g1 x := by
  have he := tsum_bilinear_unitFourierCoefficient hf hg1
  simp only [unitFourierCoefficient_prescribed_periodic_derivative g g1 hg hg1 hdg hgp] at he
  rw [gardnerBivector_eq_tsum,← he,
    ← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => unitFourierCoefficient f (-k)*
      (2*I*(Real.pi:ℂ)*k*unitFourierCoefficient g k))]
  apply tsum_congr
  intro k
  simp only [ha,hb,Equiv.neg_apply,neg_neg,Int.cast_neg]
  ring

end NLS.Poisson
