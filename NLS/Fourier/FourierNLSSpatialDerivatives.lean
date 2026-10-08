import NLS.Fourier.PeriodOneSynthesisAlgebra
import NLS.Fourier.LocalNLSExistence
import NLS.Fourier.PeriodOneSmoothSynthesis

/-! # Spatial derivatives and the physical Schrödinger term

Two weighted ℓ¹ orders supply both derivative series. Their bounded
coefficient multipliers synthesize to actual classical spatial derivatives.
-/
noncomputable section
open Complex
namespace NLS.Fourier

/-- The spatial derivative symbol for the original unit-period coefficients. -/
def nlsSpatialSymbol (n : ℤ) : ℂ := 2*I*(Real.pi : ℂ)*n

@[simp] theorem norm_nlsSpatialSymbol (n : ℤ) :
    ‖nlsSpatialSymbol n‖ = (2*Real.pi)*|(n : ℝ)| := by
  simp [nlsSpatialSymbol,Real.pi_pos.le,abs_of_nonneg]

/-- The first spatial derivative, bounded from order two to the raw ℓ¹ space. -/
def nlsFirstDerivativeCLM :
    WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1 →L[ℂ]
      WeightedCoeff SpectralWeight.one.toWeight 1 :=
  WeightedCoeff.weightedMultiplierCLM _ _ nlsSpatialSymbol (2*Real.pi) (by positivity) (by
    intro n
    simp only [SpectralWeight.one_apply,one_mul,norm_nlsSpatialSymbol,
      SpectralWeight.sobolev_apply,Weight.sobolev_apply,Real.rpow_two]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [abs_nonneg (n : ℝ)])

@[simp] theorem nlsFirstDerivativeCLM_apply
    (a : WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1) (n : ℤ) :
    (nlsFirstDerivativeCLM a).val n = nlsSpatialSymbol n*a.val n := rfl

/-- The second spatial derivative, with the exact squared Fourier symbol. -/
def nlsSecondDerivativeCLM :
    WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1 →L[ℂ]
      WeightedCoeff SpectralWeight.one.toWeight 1 :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun n => (nlsSpatialSymbol n)^2)
    ((2*Real.pi)^2) (by positivity) (by
      intro n
      simp only [SpectralWeight.one_apply,one_mul,norm_pow,norm_nlsSpatialSymbol,
        SpectralWeight.sobolev_apply,Weight.sobolev_apply,Real.rpow_two,mul_pow]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [abs_nonneg (n : ℝ)])

@[simp] theorem nlsSecondDerivativeCLM_apply
    (a : WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1) (n : ℤ) :
    (nlsSecondDerivativeCLM a).val n = (nlsSpatialSymbol n)^2*a.val n := rfl

/-- The original linear NLS velocity as a bounded map losing two orders. -/
def nlsLinearCLM :
    WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1 →L[ℂ]
      WeightedCoeff SpectralWeight.one.toWeight 1 := I • nlsSecondDerivativeCLM

@[simp] theorem nlsLinearCLM_apply
    (a : WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1) (n : ℤ) :
    (nlsLinearCLM a).val n = nlsLinearSymbol n*a.val n := by
  change I*((nlsSpatialSymbol n)^2*a.val n) = _
  simp only [nlsSpatialSymbol,nlsLinearSymbol]
  push_cast
  simp only [mul_pow,I_sq]
  ring

/-- Differentiating the physical series once gives the first derivative multiplier. -/
theorem deriv_periodOneSynthesis_sobolevTwo
    (a : WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1) :
    deriv (periodOneSynthesis ((SpectralWeight.sobolev 2 (by norm_num)).toCoeff a)) =
      periodOneSynthesis (SpectralWeight.one.toCoeff (nlsFirstDerivativeCLM a)) := by
  funext x
  apply (hasDerivAt_periodOneSynthesis_of_coefficients _ _ _ x).deriv
  intro n
  simp only [SpectralWeight.toCoeff_apply,nlsFirstDerivativeCLM_apply,nlsSpatialSymbol]

/-- The second classical derivative is the absolutely convergent second derivative series. -/
theorem deriv_deriv_periodOneSynthesis_sobolevTwo
    (a : WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1) :
    deriv (deriv (periodOneSynthesis ((SpectralWeight.sobolev 2 (by norm_num)).toCoeff a))) =
      periodOneSynthesis (SpectralWeight.one.toCoeff (nlsSecondDerivativeCLM a)) := by
  rw [deriv_periodOneSynthesis_sobolevTwo]
  funext x
  apply (hasDerivAt_periodOneSynthesis_of_coefficients _ _ _ x).deriv
  intro n
  simp only [SpectralWeight.toCoeff_apply,nlsFirstDerivativeCLM_apply,nlsSecondDerivativeCLM_apply,nlsSpatialSymbol]
  ring

/-- The quadratic Fourier NLS term is exactly `i` times the second spatial derivative. -/
theorem periodOneSynthesis_nlsLinearCLM
    (a : WeightedCoeff (SpectralWeight.sobolev 2 (by norm_num)).toWeight 1) (x : ℝ) :
    periodOneSynthesis (SpectralWeight.one.toCoeff (nlsLinearCLM a)) x =
      I*deriv (deriv (periodOneSynthesis ((SpectralWeight.sobolev 2 (by norm_num)).toCoeff a))) x := by
  rw [deriv_deriv_periodOneSynthesis_sobolevTwo]
  change periodOneSynthesis (SpectralWeight.one.toCoeff (I • nlsSecondDerivativeCLM a)) x = _
  rw [map_smul,periodOneSynthesis_smul]

end NLS.Fourier
