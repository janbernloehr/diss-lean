import NLS.KdV.RiccatiEnergy
import NLS.Fourier.PeriodOneContinuousMean
import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian

/-! # Physical KdV energy on the full complex period-one H1 space -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

/-- The cubic term is the literal physical mean, without conjugation. -/
def sobolevKdVCubic (q : ScalarDomain 2) : ℂ :=
  continuousCircleMean ((periodOneSobolevSynthesis q)^3)

/-- The complexified physical KdV energy with kinetic coefficient one half. -/
def sobolevKdVHamiltonian (q : ScalarDomain 2) : ℂ :=
  periodOneSobolevKinetic (q,q)/2+sobolevKdVCubic q

theorem analyticAt_sobolevKdVHamiltonian (q : ScalarDomain 2) :
    AnalyticAt ℂ sobolevKdVHamiltonian q := by
  have hk : AnalyticAt ℂ (fun q : ScalarDomain 2 => periodOneSobolevKinetic (q,q)) q :=
    (analyticAt_periodOneSobolevKinetic (q,q)).comp (f := fun u : ScalarDomain 2 => (u,u))
      (analyticAt_id.prod analyticAt_id)
  have hc : AnalyticAt ℂ sobolevKdVCubic q :=
    (continuousCircleMean.analyticAt _).comp ((periodOneSobolevSynthesis.analyticAt q).pow 3)
  exact hk.div_const.add hc

theorem continuous_sobolevKdVHamiltonian : Continuous sobolevKdVHamiltonian :=
  continuous_iff_continuousAt.mpr (fun q => (analyticAt_sobolevKdVHamiltonian q).continuousAt)

theorem sobolevKdVCubic_eq_integral (q : ScalarDomain 2) :
    sobolevKdVCubic q = ∫ x in (0 : ℝ)..1,
      (periodOneSobolevSynthesis q (x : AddCircle (2 : ℝ)))^3 := by
  apply continuousCircleMean_eq_periodOne_integral
  intro x
  change (periodOneSobolevSynthesis q ((x+1 : ℝ) : AddCircle (2 : ℝ)))^3 = _
  exact congrArg (fun z : ℂ => z^3) (periodOneSobolevSynthesis_periodic q x)

/-- This agrees with the actual weak-H1 physical integral: the classical
derivative is defined almost everywhere and is square integrable. -/
theorem sobolevKdVHamiltonian_eq_integral (q : ScalarDomain 2) :
    sobolevKdVHamiltonian q = classicalHamiltonian
      (fun x : ℝ => periodOneSobolevSynthesis q (x : AddCircle (2 : ℝ))) := by
  rw [sobolevKdVHamiltonian,periodOneSobolevKinetic_eq_integral,sobolevKdVCubic_eq_integral]
  unfold classicalHamiltonian
  rw [←intervalIntegral.integral_div]
  simp only [pow_two]
  symm
  apply intervalIntegral.integral_add
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
    exact ((memLp_deriv_periodOneSobolevSynthesis q).integrable_mul
      (memLp_deriv_periodOneSobolevSynthesis q)).div_const 2
  · exact ((continuous_periodOneSobolevSynthesis q).pow 3).intervalIntegrable 0 1

theorem tendsto_sobolevKdVHamiltonian_truncate (q : ScalarDomain 2) :
    Tendsto (fun S : Finset ℤ => sobolevKdVHamiltonian
      (WeightedCoeff.truncate (Weight.sobolev 1) 2 S q)) atTop (nhds (sobolevKdVHamiltonian q)) :=
  (continuous_sobolevKdVHamiltonian.tendsto q).comp
    (WeightedCoeff.tendsto_truncate _ 2 (by simp) q)

end NLS.KdV
