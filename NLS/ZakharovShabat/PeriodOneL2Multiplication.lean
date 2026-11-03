import NLS.ZakharovShabat.PeriodOneSobolevProductPairing

/-! # Bounded multiplication by an H¹ coefficient field on physical L²

The actual Fourier product is self-transpose in the physical bilinear
pairing, is associative with H¹ products, and retains the exact Leibniz
rule. Density extends these identities to arbitrary infinite L² inputs.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

def periodOneL2Multiplication : ScalarDomain 2 →L[ℂ] Coeff 2 →L[ℂ] Coeff 2 :=
  (Coeff.convolutionCLM (p := 2)).flip.comp (WeightedCoeff.sobolevToL1CLM 2 (by simp))

theorem periodOneL2Multiplication_inclusion (a b : ScalarDomain 2) :
    periodOneL2Multiplication a (scalarInclusion b) = scalarInclusion (periodOneSobolevProduct a b) := by
  change Coeff.convolution (scalarInclusion b) (WeightedCoeff.sobolevToL1CLM 2 (by simp) a) = _
  rw [← scalarInclusion_periodOneSobolevProduct,periodOneSobolevProduct_comm b a]

theorem periodOneSobolevProduct_assoc (a b c : ScalarDomain 2) :
    periodOneSobolevProduct a (periodOneSobolevProduct b c) =
      periodOneSobolevProduct (periodOneSobolevProduct a b) c := by
  have he : (fun x : ℝ => periodOneSobolevSynthesis (periodOneSobolevProduct a (periodOneSobolevProduct b c))
      (x : AddCircle (2 : ℝ))) =
      fun x : ℝ => periodOneSobolevSynthesis (periodOneSobolevProduct (periodOneSobolevProduct a b) c)
        (x : AddCircle (2 : ℝ)) := by
    funext x
    rw [periodOneSobolevSynthesis_product,periodOneSobolevSynthesis_product,
      periodOneSobolevSynthesis_product,periodOneSobolevSynthesis_product]
    ring
  apply Subtype.ext
  funext n
  have hc := congrArg (fun f : ℝ → ℂ => periodOneCoefficient f n) he
  simpa only [periodOneCoefficient_periodOneSobolevSynthesis] using hc

theorem reflectedHilbertPairing_L2Multiplication (u : ScalarDomain 2) (f h : Coeff 2) :
    reflectedHilbertPairing f (periodOneL2Multiplication u h) =
      reflectedHilbertPairing (periodOneL2Multiplication u f) h := by
  have hF : Continuous (fun z : Coeff 2 × Coeff 2 => reflectedHilbertPairing z.1 (periodOneL2Multiplication u z.2)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((reflectedHilbertPairing.analyticAt_bilinear _).comp₂ analyticAt_fst
      ((periodOneL2Multiplication u).analyticAt _ |>.comp analyticAt_snd)).continuousAt
  have hG : Continuous (fun z : Coeff 2 × Coeff 2 => reflectedHilbertPairing (periodOneL2Multiplication u z.1) z.2) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((reflectedHilbertPairing.analyticAt_bilinear _).comp₂
      ((periodOneL2Multiplication u).analyticAt _ |>.comp analyticAt_fst) analyticAt_snd).continuousAt
  have hd := (scalarInclusion_denseRange (p := 2) (by simp)).prodMap
    (scalarInclusion_denseRange (p := 2) (by simp))
  have he := hd.equalizer hF hG (by
    funext z
    change reflectedHilbertPairing (scalarInclusion z.1) (periodOneL2Multiplication u (scalarInclusion z.2)) =
      reflectedHilbertPairing (periodOneL2Multiplication u (scalarInclusion z.1)) (scalarInclusion z.2)
    rw [periodOneL2Multiplication_inclusion,periodOneL2Multiplication_inclusion]
    exact reflectedHilbertPairing_sobolevProduct u z.1 z.2)
  exact congrFun he (f,h)

theorem periodOneL2Multiplication_assoc (u v : ScalarDomain 2) (h : Coeff 2) :
    periodOneL2Multiplication u (periodOneL2Multiplication v h) =
      periodOneL2Multiplication (periodOneSobolevProduct u v) h := by
  have he := (scalarInclusion_denseRange (p := 2) (by simp)).equalizer
    ((periodOneL2Multiplication u).continuous.comp (periodOneL2Multiplication v).continuous)
    (periodOneL2Multiplication (periodOneSobolevProduct u v)).continuous (by
      funext a
      change periodOneL2Multiplication u (periodOneL2Multiplication v (scalarInclusion a)) =
        periodOneL2Multiplication (periodOneSobolevProduct u v) (scalarInclusion a)
      rw [periodOneL2Multiplication_inclusion,periodOneL2Multiplication_inclusion,
        periodOneL2Multiplication_inclusion,periodOneSobolevProduct_assoc])
  exact congrFun he h

theorem periodOneDerivative_product_L2 (a b : ScalarDomain 2) :
    periodOneDerivative (periodOneSobolevProduct a b) =
      periodOneL2Multiplication b (periodOneDerivative a)+periodOneL2Multiplication a (periodOneDerivative b) := by
  rw [periodOneDerivative_periodOneSobolevProduct]
  change Coeff.convolution (periodOneDerivative a) (WeightedCoeff.sobolevToL1CLM 2 (by simp) b)+_ =
    Coeff.convolution (periodOneDerivative a) (WeightedCoeff.sobolevToL1CLM 2 (by simp) b)+_
  congr 1
  exact (Coeff.youngConvolution_comm (show YoungRelation 1 2 2 by simp [YoungRelation]) _ _).trans
    (Coeff.youngConvolution_eq_convolution _ _ _)

end NLS.ZakharovShabat
