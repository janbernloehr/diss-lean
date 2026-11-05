import NLS.SequenceSpaces.YoungConvolution
import NLS.Fourier.PeriodOneSobolev
import NLS.Fourier.PeriodOneSynthesisAlgebra
import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra
import NLS.MKdV.MiuraClassicalSolution

/-! # The literal period-one Miura potential on the full complex H¹ space

Its coefficients are 2*pi*i*n*u_n plus the actual convolution of u with
itself. The map takes values in L², is analytic in the original H¹ norm,
and its actual Fourier integrals equal those of u'+u² on every H¹ input.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Fourier

theorem periodOneCoefficient_add_of_intervalIntegrable (f g : ℝ → ℂ)
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1) (n : ℤ) :
    periodOneCoefficient (f+g) n = periodOneCoefficient f n+periodOneCoefficient g n := by
  simp only [← unitFourierCoefficient_eq_fourierCoeffOn,periodOneCoefficient]
  simp only [unitFourierCoefficient,Pi.add_apply,add_mul]
  exact intervalIntegral.integral_add
    (hf.mul_continuousOn (continuous_wave _).continuousOn)
    (hg.mul_continuousOn (continuous_wave _).continuousOn)

end NLS.Fourier
namespace NLS.MKdV

def sobolevMiuraUnitPotential (a : ScalarDomain 2) : Coeff 2 :=
  (2 : ℂ) • derivative a +
    Coeff.convolution (scalarInclusion a) (WeightedCoeff.sobolevToL1CLM 2 (by simp) a)

theorem sobolevMiuraUnitPotential_apply (a : ScalarDomain 2) (n : ℤ) :
    sobolevMiuraUnitPotential a n = 2*I*(Real.pi : ℂ)*n*a.val n+
      ∑' k : ℤ, a.val (n-k)*a.val k := by
  simp only [sobolevMiuraUnitPotential,lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,Pi.smul_apply,
    smul_eq_mul,derivative_apply,Coeff.convolution_apply,scalarInclusion_apply,
    WeightedCoeff.sobolevToL1CLM_apply]
  ring

theorem analyticAt_sobolevMiuraUnitPotential (a : ScalarDomain 2) :
    AnalyticAt ℂ sobolevMiuraUnitPotential a := by
  have hC : AnalyticAt ℂ (fun p : Coeff 2 × Coeff 1 => Coeff.convolution p.1 p.2)
      (scalarInclusion a,WeightedCoeff.sobolevToL1CLM 2 (by simp) a) :=
    (Coeff.convolutionCLM (p := 2)).analyticAt_bilinear _
  exact ((derivative.analyticAt a).const_smul (c := (2 : ℂ))).add
    (hC.comp (f := fun b : ScalarDomain 2 =>
      (scalarInclusion b,WeightedCoeff.sobolevToL1CLM 2 (by simp) b))
      ((scalarInclusion.analyticAt a).prod
        ((WeightedCoeff.sobolevToL1CLM 2 (by simp)).analyticAt a)))

theorem sobolevMiuraUnitPotential_physical (a : ScalarDomain 2) (n : ℤ) :
    sobolevMiuraUnitPotential a n = periodOneCoefficient
      (miuraPotential (fun x => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)))) n := by
  let f : ℝ → ℂ := fun x => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))
  let b := WeightedCoeff.sobolevToL1CLM 2 (by simp) a
  have hsquare : (fun x => f x^2) = periodOneSynthesis (Coeff.convolution b b) := by
    funext x
    rw [periodOneSynthesis_convolution]
    change f x^2 = f x*f x
    exact pow_two (f x)
  have hc : Continuous f := continuous_periodOneSobolevSynthesis a
  have hi : IntervalIntegrable (deriv f) volume 0 1 := intervalIntegrable_deriv_periodOneSobolevSynthesis a
  change _ = periodOneCoefficient (deriv f+(fun x => f x^2)) n
  have hsqi : IntervalIntegrable (fun x => f x^2) volume 0 1 := (hc.pow 2).intervalIntegrable 0 1
  have hadd := periodOneCoefficient_add_of_intervalIntegrable (deriv f) (fun x => f x^2) hi hsqi n
  have hsqc : periodOneCoefficient (fun x => f x^2) n = ∑' k : ℤ, a.val (n-k)*a.val k := by
    rw [hsquare,periodOneCoefficient_synthesis,Coeff.convolution_apply]
    simp only [b,WeightedCoeff.sobolevToL1CLM_apply]
  have hdc : periodOneCoefficient (deriv f) n = 2*I*(Real.pi : ℂ)*n*a.val n :=
    periodOneCoefficient_deriv_periodOneSobolevSynthesis a n
  exact (sobolevMiuraUnitPotential_apply a n).trans ((congrArg₂ (fun x y : ℂ => x+y) hdc hsqc).symm.trans hadd.symm)

/-- Original period-one coefficients inserted at the even ambient-circle
indices of the shared Hill operator. -/
def sobolevMiuraHillPotential (a : ScalarDomain 2) : Coeff 2 :=
  Coeff.periodDouble (sobolevMiuraUnitPotential a)

theorem analyticAt_sobolevMiuraHillPotential (a : ScalarDomain 2) :
    AnalyticAt ℂ sobolevMiuraHillPotential a :=
  ((Coeff.periodDouble (p := 2)).toContinuousLinearMap.analyticAt _).comp
    (analyticAt_sobolevMiuraUnitPotential a)

theorem sobolevMiuraHillPotential_even (a : ScalarDomain 2) :
    sobolevMiuraHillPotential a ∈ Coeff.paritySubspace 0 := Coeff.periodDouble_mem _

end NLS.MKdV
