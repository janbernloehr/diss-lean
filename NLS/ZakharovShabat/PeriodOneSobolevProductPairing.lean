import NLS.ZakharovShabat.PeriodOneSobolevProduct
import NLS.Fourier.PeriodOneSynthesisAlgebra
import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian

/-! # Physical multiplication and its bilinear L² transpose

The bounded H¹ Fourier product is literal pointwise multiplication of
the original continuous representatives. Parseval gives its exact
transpose in the physical unconjugated pairing.
-/
noncomputable section
open NLS.Poisson
open Set Complex MeasureTheory NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem periodOneSobolevProduct_toL1 (a b : ScalarDomain 2) :
    WeightedCoeff.sobolevToL1CLM 2 (by simp) (periodOneSobolevProduct a b) =
      Coeff.convolution (WeightedCoeff.sobolevToL1CLM 2 (by simp) a)
        (WeightedCoeff.sobolevToL1CLM 2 (by simp) b) := by
  ext n
  simp only [WeightedCoeff.sobolevToL1CLM_apply,periodOneSobolevProduct_apply,Coeff.convolution_apply]

theorem periodOneSobolevSynthesis_product (a b : ScalarDomain 2) (x : ℝ) :
    periodOneSobolevSynthesis (periodOneSobolevProduct a b) (x : AddCircle (2 : ℝ)) =
      periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))*periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)) := by
  rw [periodOneSobolevSynthesis_apply,periodOneSobolevProduct_toL1,periodOneSynthesis_convolution,
    periodOneSobolevSynthesis_apply,periodOneSobolevSynthesis_apply]

theorem reflectedHilbertPairing_sobolevProduct (u f h : ScalarDomain 2) :
    reflectedHilbertPairing (scalarInclusion f) (scalarInclusion (periodOneSobolevProduct u h)) =
      reflectedHilbertPairing (scalarInclusion (periodOneSobolevProduct u f)) (scalarInclusion h) := by
  have hpair (a b : ScalarDomain 2) : reflectedHilbertPairing (scalarInclusion a) (scalarInclusion b) =
      periodOneSobolevMass (a,b) := by
    simp only [reflectedHilbertPairing_apply,periodOneSobolevMass,Coeff.dualPairing_apply,
      Coeff.reflection_apply,scalarInclusion_apply]
    simpa only [Equiv.neg_apply,neg_neg] using
      (Equiv.neg ℤ).tsum_eq (fun n : ℤ => a.val (-n)*b.val n)
  rw [hpair,hpair]
  rw [periodOneSobolevMass_eq_integral,periodOneSobolevMass_eq_integral]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [periodOneSobolevSynthesis_product,periodOneSobolevSynthesis_product]
  ring

end NLS.ZakharovShabat
