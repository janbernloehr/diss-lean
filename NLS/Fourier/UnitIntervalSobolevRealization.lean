import NLS.Fourier.UnitIntervalL2Product
import NLS.Fourier.PeriodOneSobolev

/-! # Exact interval L2 realizations of unit-period H1 operations

The domain inclusion, physical derivative and rough-potential multiplier
all retain their original coefficients and the unit-period factor two.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier
open NLS.ZakharovShabat

/-- Equality of all original unit Fourier integrals identifies the actual L2 representative. -/
theorem unitL2Synthesis_eq_of_unitCoefficients (a : Coeff 2) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hc : ∀ n : ℤ, unitFourierCoefficient f n = a n) :
    unitL2SynthesisEquiv a =ᵐ[volume.restrict (Ioc 0 1)] f := by
  have he : unitIntervalMemLpCoefficients f hf = a := by
    ext n
    rw [unitIntervalMemLpCoefficients_apply,
      ← unitFourierCoefficient_eq_intervalFourierCoefficient]
    exact hc n
  rw [← he, unitL2SynthesisEquiv_memLpCoefficients]
  exact hf.coeFn_toLp

/-- The unit-period H1 domain inclusion is the same interval L2 function. -/
theorem unitL2Synthesis_scalarInclusion (a : ScalarDomain 2) :
    unitL2SynthesisEquiv (scalarInclusion a) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))) := by
  apply unitL2Synthesis_eq_of_unitCoefficients
  · exact memLp_two_interval (continuous_periodOneSobolevSynthesis a) 0 1 (by norm_num)
  · intro n
    rw [unitFourierCoefficient_eq_fourierCoeffOn]
    rw [scalarInclusion_apply]
    change periodOneCoefficient _ n = a.val n
    exact periodOneCoefficient_periodOneSobolevSynthesis a n

/-- The original unit-period derivative is exactly twice the period-two symbol. -/
theorem unitL2Synthesis_unitDerivative (a : ScalarDomain 2) :
    unitL2SynthesisEquiv ((2:ℂ) • derivative a) =ᵐ[volume.restrict (Ioc 0 1)]
      deriv (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))) := by
  apply unitL2Synthesis_eq_of_unitCoefficients
  · exact memLp_deriv_periodOneSobolevSynthesis a
  · intro n
    rw [unitFourierCoefficient_eq_fourierCoeffOn]
    change periodOneCoefficient _ n = 2*derivative a n
    rw [periodOneCoefficient_deriv_periodOneSobolevSynthesis, derivative_apply]
    ring

/-- The H1 multiplier with an arbitrary L2 potential is actual physical multiplication. -/
theorem unitL2Synthesis_potentialMul (u : Coeff 2) (a : ScalarDomain 2) :
    unitL2SynthesisEquiv (potentialMul (by norm_num) u a) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x : ℝ => unitL2SynthesisEquiv u x*
        periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))) := by
  let Y := fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))
  have hYc : Continuous Y := continuous_periodOneSobolevSynthesis a
  have hYm := memLp_two_interval hYc 0 1 (by norm_num)
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hYc.continuousOn
  apply unitL2Synthesis_eq_of_unitCoefficients
  · simpa only [mul_comm] using memLp_unitInterval_bounded_mul (unitL2SynthesisEquiv u) Y
      (Lp.memLp _) hYc K hK
  · intro n
    rw [unitFourierCoefficient_L2_product _ _ (Lp.memLp _) hYm, potentialMul_apply]
    apply tsum_congr
    intro k
    rw [unitFourierCoefficient_eq_fourierCoeffOn,
      unitFourierCoefficient_eq_fourierCoeffOn]
    change periodOneCoefficient (unitL2SynthesisEquiv u) (n-k)*periodOneCoefficient Y k = _
    have hu : periodOneCoefficient (unitL2SynthesisEquiv u) (n-k) = u (n-k) := by
      change fourierCoeffOn (by norm_num : (0:ℝ)<1) (unitL2SynthesisEquiv u) (n-k) = _
      rw [← intervalFourierCoefficient_eq_fourierCoeffOn]
      exact unitL2SynthesisLinear_coefficient u (n-k)
    rw [hu]
    exact congrArg (fun z => u (n-k)*z) (periodOneCoefficient_periodOneSobolevSynthesis a k)

end NLS.Fourier
