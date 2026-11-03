import NLS.KdV.SingularHillPhysicalL2
import NLS.Fourier.ArbitraryPeriodBilinearParseval
import NLS.Fourier.IntervalL2Realization

/-! The full original periodic dual pairing is the literal physical
bilinear integral with source normalization ONE HALF. No period-one or
reality condition is imposed on physical inputs or domain vectors. -/
noncomputable section
open Set MeasureTheory
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- Every physical periodic L2 norm retains exactly the source half-integral. -/
theorem norm_sq_singularHillPhysicalL2 (F : CircleL2) :
    ‖F‖^2 = (1/2:ℝ) * ∫ x in (0:ℝ)..2, ‖circlePullback F x‖^2 := by
  have he : periodTwoL2Coefficients (circlePullback F) (memLp_circlePullback F) =
      l2Synthesis.symm F := by
    ext n
    rw [periodTwoL2Coefficients_apply,periodTwoCoefficient_circlePullback]
    exact (fourierBasis_repr F n).symm
  have hp := norm_sq_periodTwoL2Coefficients (circlePullback F) (memLp_circlePullback F)
  rw [he,LinearIsometryEquiv.norm_map] at hp
  exact hp

/-- The entire original dual evaluation is the reflected unweighted L2 pairing. -/
theorem singularHillL2BaseInclusion_coefficientPairing (F : CircleL2)
    (g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (singularHillL2BaseInclusion F) g =
      Coeff.dualPairing (Coeff.reflection (l2Synthesis.symm F)) (h1L2Coefficients g) := by
  change sobolevDualIsometry 1 (by norm_num) (singularHillL2BaseInclusion F) g = _
  rw [sobolevDualIsometry_apply,Coeff.dualPairing_apply]
  apply tsum_congr
  intro n
  rw [Coeff.reflection_apply,h1L2Coefficients_apply]
  have he := singularHillL2BaseInclusion_coefficient F (-n)
  simp only [neg_neg] at he
  rw [he,mul_comm]

/-- Source-normalized Cauchy--Schwarz on the actual original dual evaluation. -/
theorem norm_singularHillL2BaseInclusion_pairing_le (F : CircleL2)
    (g : FourierLebesgueSpace (2:ℝ) 1 2) :
    ‖singularHillPairing (singularHillL2BaseInclusion F) g‖ ≤
      ‖F‖ * ‖singularHillL2DomainInclusion g‖ := by
  rw [singularHillL2BaseInclusion_coefficientPairing,norm_singularHillL2DomainInclusion]
  have hb := Coeff.norm_dualPairing_le (Coeff.reflection (l2Synthesis.symm F))
    (h1L2Coefficients g)
  simpa only [LinearIsometryEquiv.norm_map] using hb

/-- Exact original physical pairing: the factor ONE HALF belongs to the
periodic source normalization and is retained for arbitrary complex data. -/
theorem singularHillL2BaseInclusion_physical_pairing (F : CircleL2)
    (g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (singularHillL2BaseInclusion F) g =
      (2:ℂ)⁻¹ * ∫ x in (0:ℝ)..2,
        circlePullback F x * circlePullback (singularHillL2DomainInclusion g) x := by
  have hs := hasSum_bilinear_intervalFourierCoefficient (by norm_num : (0:ℝ) < 2)
    (memLp_circlePullback F) (memLp_circlePullback (singularHillL2DomainInclusion g))
  simp only [intervalFourierCoefficient_two,periodTwoCoefficient_circlePullback] at hs
  simp only [Complex.ofReal_ofNat] at hs
  rw [← hs.tsum_eq,singularHillL2BaseInclusion_coefficientPairing,Coeff.dualPairing_apply]
  apply tsum_congr
  intro n
  rw [Coeff.reflection_apply,h1L2Coefficients_apply,
    singularHillL2DomainInclusion_coefficient,← fourierBasis_repr]
  rfl

/-- The original domain mass is the same literal half-integral. -/
theorem singularHillDomainInclusion_physical_pairing
    (f g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (singularHillDomainInclusion f) g =
      (2:ℂ)⁻¹ * ∫ x in (0:ℝ)..2,
        circlePullback (singularHillL2DomainInclusion f) x *
          circlePullback (singularHillL2DomainInclusion g) x := by
  rw [← singularHillL2BaseInclusion_domain f,singularHillL2BaseInclusion_physical_pairing]

end NLS.KdV
