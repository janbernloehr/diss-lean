import NLS.KdV.SingularHillRieszContinuous
import NLS.KdV.SingularHillBilinear
import NLS.Fourier.ArbitraryPeriodBilinearParseval
import NLS.Fourier.SobolevDerivative

/-! Physical original H1 multiplication, mass and free weak energy.
Both the complex bilinear convention and the normalized factor one half remain explicit. -/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The actual H1 representative is the same Wiener representative. -/
theorem singularHillContinuousDomainInclusion_eq_Wiener
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillContinuousDomainInclusion f = continuousRepresentative (sobolevToWiener (by norm_num) f) := by
  apply continuousFourierCLM_injective
  ext n
  simp only [continuousFourierCLM_apply]
  change fourierCoeff (sobolevSynthesis (by simp) (sobolevCoefficients 1 2 f)) n =
    fourierCoeff (continuousRepresentative (sobolevToWiener (by norm_num) f)) n
  rw [fourierCoeff_sobolevSynthesis,
    continuousRepresentative_coefficient,sobolevToWiener_coefficient]
  rfl

/-- The physical full-domain representative is faithful. -/
theorem singularHillContinuousDomainInclusion_injective :
    Function.Injective singularHillContinuousDomainInclusion := by
  intro f g h
  apply singularHillL2DomainInclusion_injective
  rw [← singularHillContinuousDomainInclusion_toLp f,← singularHillContinuousDomainInclusion_toLp g,h]

/-- Native H1 multiplication is pointwise multiplication on the actual circle. -/
theorem singularHillContinuousDomainInclusion_product
    (f g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillContinuousDomainInclusion (h1Product f g) =
      singularHillContinuousDomainInclusion f*singularHillContinuousDomainInclusion g := by
  simp only [singularHillContinuousDomainInclusion_eq_Wiener,continuousRepresentative_h1Product]

/-- The native mass is the exact half-integral of the continuous positions. -/
theorem singularHillDomainInclusion_continuous_pairing
    (f g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (singularHillDomainInclusion f) g =
      (2:ℂ)⁻¹*∫ x in (0:ℝ)..2, singularHillContinuousDomainInclusion f (x : AddCircle (2:ℝ))*
        singularHillContinuousDomainInclusion g (x : AddCircle (2:ℝ)) := by
  have hs := hasSum_bilinear_intervalFourierCoefficient (by norm_num : (0:ℝ) < 2)
    (memLp_two_interval (continuous_sobolevSynthesis (by simp) (sobolevCoefficients 1 2 f)) 0 2 (by norm_num))
    (memLp_two_interval (continuous_sobolevSynthesis (by simp) (sobolevCoefficients 1 2 g)) 0 2 (by norm_num))
  simp only [intervalFourierCoefficient_two,periodTwoCoefficient_sobolevSynthesis,
    sobolevCoefficients_apply,neg_neg,Complex.ofReal_ofNat] at hs
  change HasSum _ ((2:ℂ)⁻¹*∫ x in (0:ℝ)..2,
    singularHillContinuousDomainInclusion f (x : AddCircle (2:ℝ))*
      singularHillContinuousDomainInclusion g (x : AddCircle (2:ℝ))) at hs
  rw [← hs.tsum_eq,singularHillPairing,sobolevDualIsometry_apply]
  apply tsum_congr
  intro n
  rw [singularHillDomainInclusion_val,mul_comm]

/-- The native Laplacian weak form is the EXACT physical derivative
product integral, on the ENTIRE H1 domain and with no boundary integration assumption. -/
theorem singularHillLaplacian_continuous_pairing
    (f g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (singularHillLaplacian f) g =
      (2:ℂ)⁻¹*∫ x in (0:ℝ)..2,
        deriv (fun y : ℝ => singularHillContinuousDomainInclusion f (y : AddCircle (2:ℝ))) x*
          deriv (fun y : ℝ => singularHillContinuousDomainInclusion g (y : AddCircle (2:ℝ))) x := by
  have hs := hasSum_bilinear_intervalFourierCoefficient (by norm_num : (0:ℝ) < 2)
    (memLp_deriv_sobolevSynthesis (sobolevCoefficients 1 2 f))
    (memLp_deriv_sobolevSynthesis (sobolevCoefficients 1 2 g))
  simp only [intervalFourierCoefficient_two,periodTwoCoefficient_deriv_sobolevSynthesis,
    sobolevCoefficients_apply,neg_neg,Complex.ofReal_ofNat,Int.cast_neg] at hs
  change HasSum _ ((2:ℂ)⁻¹*∫ x in (0:ℝ)..2,
    deriv (fun y : ℝ => singularHillContinuousDomainInclusion f (y : AddCircle (2:ℝ))) x*
      deriv (fun y : ℝ => singularHillContinuousDomainInclusion g (y : AddCircle (2:ℝ))) x) at hs
  rw [← hs.tsum_eq,singularHillPairing,sobolevDualIsometry_apply]
  apply tsum_congr
  intro n
  rw [show n = -(-n) by omega,singularHillLaplacian_coefficient,freeHillValue_neg]
  simp only [freeHillValue,ofReal_mul,ofReal_pow,neg_neg]
  push_cast
  ring_nf
  simp only [I_sq]
  ring

end NLS.KdV
