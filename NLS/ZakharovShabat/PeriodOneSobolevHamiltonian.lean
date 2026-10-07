import NLS.Fourier.PeriodOneSobolev
import NLS.Fourier.IntervalBilinearParseval
import NLS.SequenceSpaces.ConjugateDuality
import Mathlib.Analysis.Analytic.Constructions

/-! # Physical mass and NLS energy on the full period-one H¹ space

The bounded bilinear Fourier pairing defines the mass and kinetic energy.
The quartic term is the mean of the product of the continuous representatives.
All three are complex analytic on the full product Sobolev space, and their
sum agrees with the physical unit-interval integral using classical derivatives.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.ZakharovShabat
open Fourier

/-- Period-one differentiation of original coefficients. -/
def periodOneDerivative : ScalarDomain 2 →L[ℂ] Coeff 2 := (2 : ℂ) • derivative

@[simp] theorem periodOneDerivative_apply (a : ScalarDomain 2) (n : ℤ) :
    periodOneDerivative a n = 2 * Complex.I * (Real.pi : ℂ) * n * a.val n := by
  change (2 : ℂ) * (Complex.I * (Real.pi : ℂ) * n * a.val n) = _
  ring

/-- The physical mass, extended complex bilinearly. -/
def periodOneSobolevMass (ab : ScalarDomain 2 × ScalarDomain 2) : ℂ :=
  Coeff.dualPairing (Coeff.reflection (scalarInclusion ab.1)) (scalarInclusion ab.2)

/-- The physical kinetic energy, with the period-one derivative multiplier. -/
def periodOneSobolevKinetic (ab : ScalarDomain 2 × ScalarDomain 2) : ℂ :=
  Coeff.dualPairing (Coeff.reflection (periodOneDerivative ab.1)) (periodOneDerivative ab.2)

private theorem unitCoefficient_eq_periodOneCoefficient (f : ℝ → ℂ) (n : ℤ) :
    unitFourierCoefficient f n = periodOneCoefficient f n :=
  unitFourierCoefficient_eq_fourierCoeffOn f n

private def circleMean : C(AddCircle (2 : ℝ), ℂ) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).comp continuousFourierCLM

/-- The quartic physical interaction. -/
def periodOneSobolevQuartic (ab : ScalarDomain 2 × ScalarDomain 2) : ℂ :=
  circleMean ((periodOneSobolevSynthesis ab.1)^2 * (periodOneSobolevSynthesis ab.2)^2)

/-- The period-one physical NLS Hamiltonian on every complex H¹ pair. -/
def periodOneSobolevHamiltonian (ab : ScalarDomain 2 × ScalarDomain 2) : ℂ :=
  periodOneSobolevKinetic ab + periodOneSobolevQuartic ab

/-- Parseval identifies the bounded coefficient mass with its actual physical integral. -/
theorem periodOneSobolevMass_eq_integral (a b : ScalarDomain 2) :
    periodOneSobolevMass (a,b) = ∫ x in (0 : ℝ)..1,
      periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)) *
        periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)) := by
  have h := tsum_bilinear_unitFourierCoefficient
    (continuous_periodOneSobolevSynthesis a) (continuous_periodOneSobolevSynthesis b)
  simpa only [unitCoefficient_eq_periodOneCoefficient,
    periodOneCoefficient_periodOneSobolevSynthesis, periodOneSobolevMass,
    Coeff.dualPairing_apply, Coeff.reflection_apply, scalarInclusion_apply] using h

/-- Parseval for the actual square-integrable classical derivatives. -/
theorem periodOneSobolevKinetic_eq_integral (a b : ScalarDomain 2) :
    periodOneSobolevKinetic (a,b) = ∫ x in (0 : ℝ)..1,
      deriv (fun t : ℝ => periodOneSobolevSynthesis a (t : AddCircle (2 : ℝ))) x *
        deriv (fun t : ℝ => periodOneSobolevSynthesis b (t : AddCircle (2 : ℝ))) x := by
  have h := tsum_bilinear_unitFourierCoefficient_of_memLp
    (memLp_deriv_periodOneSobolevSynthesis a) (memLp_deriv_periodOneSobolevSynthesis b)
  simpa only [unitCoefficient_eq_periodOneCoefficient,
    periodOneCoefficient_deriv_periodOneSobolevSynthesis, periodOneSobolevKinetic,
    Coeff.dualPairing_apply, Coeff.reflection_apply, periodOneDerivative_apply] using h

/-- Taking the mean of the continuous quartic product is integration over one physical period. -/
theorem periodOneSobolevQuartic_eq_integral (a b : ScalarDomain 2) :
    periodOneSobolevQuartic (a,b) = ∫ x in (0 : ℝ)..1,
      (periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)))^2 *
        (periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)))^2 := by
  let f := (periodOneSobolevSynthesis a)^2 * (periodOneSobolevSynthesis b)^2
  let g := fun x : ℝ => f (x : AddCircle (2 : ℝ))
  have hp : Function.Periodic g 1 := by
    intro x
    change (periodOneSobolevSynthesis a ((x+1 : ℝ) : AddCircle (2 : ℝ)))^2 *
      (periodOneSobolevSynthesis b ((x+1 : ℝ) : AddCircle (2 : ℝ)))^2 = _
    exact congrArg₂ (fun u v : ℂ => u^2 * v^2)
      (periodOneSobolevSynthesis_periodic a x) (periodOneSobolevSynthesis_periodic b x)
  have hc : Continuous g := f.continuous.comp continuous_quotient_mk'
  change continuousFourierCLM f 0 = _
  rw [continuousFourierCLM_apply, ← periodTwoCoefficient_circle]
  change periodTwoCoefficient g 0 = _
  rw [show (0 : ℤ) = 2*0 by norm_num,
    periodTwoCoefficient_periodic_even g hp (hc.intervalIntegrable 0 1)]
  rw [← unitCoefficient_eq_periodOneCoefficient]
  simp only [unitFourierCoefficient, mul_zero, neg_zero, wave_zero, mul_one]
  rfl

/-- The physical kinetic and quartic integrands are both integrable for arbitrary H¹ data. -/
theorem periodOneSobolevHamiltonian_eq_integral (a b : ScalarDomain 2) :
    periodOneSobolevHamiltonian (a,b) = ∫ x in (0 : ℝ)..1,
      deriv (fun t : ℝ => periodOneSobolevSynthesis a (t : AddCircle (2 : ℝ))) x *
        deriv (fun t : ℝ => periodOneSobolevSynthesis b (t : AddCircle (2 : ℝ))) x +
      (periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)))^2 *
        (periodOneSobolevSynthesis b (x : AddCircle (2 : ℝ)))^2 := by
  rw [periodOneSobolevHamiltonian, periodOneSobolevKinetic_eq_integral,
    periodOneSobolevQuartic_eq_integral]
  symm
  apply intervalIntegral.integral_add
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
    exact (memLp_deriv_periodOneSobolevSynthesis a).integrable_mul
      (memLp_deriv_periodOneSobolevSynthesis b)
  · exact (((continuous_periodOneSobolevSynthesis a).pow 2).mul
      ((continuous_periodOneSobolevSynthesis b).pow 2)).intervalIntegrable 0 1

private theorem analyticAt_pairing (L M : ScalarDomain 2 →L[ℂ] Coeff 2)
    (ab : ScalarDomain 2 × ScalarDomain 2) :
    AnalyticAt ℂ (fun z : ScalarDomain 2 × ScalarDomain 2 =>
      Coeff.dualPairing (Coeff.reflection (L z.1)) (M z.2)) ab := by
  let A : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] Coeff 2 :=
    (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp L).comp
      (ContinuousLinearMap.fst ℂ _ _)
  let B : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] Coeff 2 :=
    M.comp (ContinuousLinearMap.snd ℂ _ _)
  exact (Coeff.dualPairing.analyticAt_bilinear (A ab, B ab)).comp (f := fun z => (A z, B z))
    ((A.analyticAt ab).prod (B.analyticAt ab))

theorem analyticAt_periodOneSobolevMass (ab : ScalarDomain 2 × ScalarDomain 2) :
    AnalyticAt ℂ periodOneSobolevMass ab := analyticAt_pairing scalarInclusion scalarInclusion ab

theorem analyticAt_periodOneSobolevKinetic (ab : ScalarDomain 2 × ScalarDomain 2) :
    AnalyticAt ℂ periodOneSobolevKinetic ab :=
  analyticAt_pairing periodOneDerivative periodOneDerivative ab

theorem analyticAt_periodOneSobolevQuartic (ab : ScalarDomain 2 × ScalarDomain 2) :
    AnalyticAt ℂ periodOneSobolevQuartic ab := by
  exact (circleMean.analyticAt _).comp
    ((((periodOneSobolevSynthesis.analyticAt _).comp analyticAt_fst).pow 2).mul
      (((periodOneSobolevSynthesis.analyticAt _).comp analyticAt_snd).pow 2))

/-- The actual physical NLS energy is complex analytic on the entire H¹ product space. -/
theorem analyticAt_periodOneSobolevHamiltonian (ab : ScalarDomain 2 × ScalarDomain 2) :
    AnalyticAt ℂ periodOneSobolevHamiltonian ab :=
  (analyticAt_periodOneSobolevKinetic ab).add (analyticAt_periodOneSobolevQuartic ab)

theorem continuous_periodOneSobolevHamiltonian : Continuous periodOneSobolevHamiltonian :=
  continuous_iff_continuousAt.mpr (fun ab => (analyticAt_periodOneSobolevHamiltonian ab).continuousAt)

theorem continuous_periodOneSobolevMass : Continuous periodOneSobolevMass :=
  continuous_iff_continuousAt.mpr (fun ab => (analyticAt_periodOneSobolevMass ab).continuousAt)

/-- Finite Fourier truncations converge in physical energy on the entire H¹ domain. -/
theorem tendsto_periodOneSobolevHamiltonian_truncate (a b : ScalarDomain 2) :
    Filter.Tendsto (fun s : Finset ℤ => periodOneSobolevHamiltonian
      (WeightedCoeff.truncate (Weight.sobolev 1) 2 s a,
       WeightedCoeff.truncate (Weight.sobolev 1) 2 s b)) Filter.atTop
      (nhds (periodOneSobolevHamiltonian (a,b))) :=
  (continuous_periodOneSobolevHamiltonian.tendsto (a,b)).comp
    ((WeightedCoeff.tendsto_truncate _ 2 (by simp) a).prodMk_nhds
      (WeightedCoeff.tendsto_truncate _ 2 (by simp) b))

end NLS.ZakharovShabat
