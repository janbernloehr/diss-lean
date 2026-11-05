import NLS.MKdV.SobolevMiuraPhysicalClass
import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian

/-! # Literal physical realization of the massive first-order Fourier operator -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.ZakharovShabat
namespace NLS.Fourier

theorem unitL2Synthesis_periodOneDerivative_representative (a : ScalarDomain 2) :
    unitL2SynthesisEquiv (periodOneDerivative a) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      deriv (fun s : ℝ => periodOneSobolevSynthesis a (s : AddCircle (2 : ℝ))) := by
  let f : ℝ → ℂ := fun s => periodOneSobolevSynthesis a (s : AddCircle (2 : ℝ))
  have hf := memLp_deriv_periodOneSobolevSynthesis a
  have he : unitIntervalMemLpCoefficients (deriv f) hf = periodOneDerivative a := by
    ext k
    rw [unitIntervalMemLpCoefficients_apply,intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num)]
    exact (periodOneCoefficient_deriv_periodOneSobolevSynthesis a k).trans
      (periodOneDerivative_apply a k).symm
  rw [← he,unitL2SynthesisEquiv_memLpCoefficients]
  exact hf.coeFn_toLp

theorem periodOneMassOperator_scalarInclusion (m : ℕ) (a : ScalarDomain 2) :
    periodOneMassOperator m (scalarInclusion a) =
      periodOneL2Inclusion (periodOneDerivative a+(((m : ℝ)+1 : ℝ) : ℂ) • scalarInclusion a) := by
  apply Subtype.ext
  funext k
  rw [periodOneMassOperator_apply,periodOneL2Inclusion_apply]
  simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    periodOneDerivative_apply,scalarInclusion_apply,periodOneMassSymbol]
  ring

theorem unitL2Synthesis_mass_representative (m : ℕ) (a : ScalarDomain 2) :
    unitL2SynthesisEquiv (periodOneDerivative a+(((m : ℝ)+1 : ℝ) : ℂ) • scalarInclusion a)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun s : ℝ => deriv (fun t : ℝ => periodOneSobolevSynthesis a (t : AddCircle (2 : ℝ))) s+
        (((m : ℝ)+1 : ℝ) : ℂ)*periodOneSobolevSynthesis a (s : AddCircle (2 : ℝ))) := by
  rw [map_add,map_smul]
  filter_upwards [Lp.coeFn_add (unitL2SynthesisEquiv (periodOneDerivative a))
      ((((m : ℝ)+1 : ℝ) : ℂ) • unitL2SynthesisEquiv (scalarInclusion a)),
    Lp.coeFn_smul ((((m : ℝ)+1 : ℝ) : ℂ)) (unitL2SynthesisEquiv (scalarInclusion a)),
    unitL2Synthesis_periodOneDerivative_representative a,
    NLS.MKdV.unitL2Synthesis_scalarInclusion_representative a] with s ha hs hd hf
  simp only [ha,Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hd,hf]

end NLS.Fourier
