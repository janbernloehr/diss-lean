import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian
import NLS.Fourier.PeriodOneCircleMean
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! The actual period-one KdV Hamiltonian on the ENTIRE complex H1 domain:
H(q)=integral_0^1 ((q_x)^2/2+q^3). Its full first variation has the original
coefficients 1 and 3. No spectral frequency or KdV flow is assumed. -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

def periodOneKdVHamiltonian (q : ScalarDomain 2) : ℂ :=
  (1/2:ℂ)*periodOneSobolevKinetic (q,q)+periodOneCircleMean ((periodOneSobolevSynthesis q)^3)

theorem analyticAt_periodOneKdVHamiltonian (q : ScalarDomain 2) :
    AnalyticAt ℂ periodOneKdVHamiltonian q := by
  have hk := (analyticAt_periodOneSobolevKinetic (q,q)).comp
    (f := fun a : ScalarDomain 2 => (a,a)) (analyticAt_id.prod analyticAt_id)
  have hc := (periodOneCircleMean.analyticAt _).comp ((periodOneSobolevSynthesis.analyticAt q).pow 3)
  exact (analyticAt_const.mul hk).add hc

theorem periodOneKdVHamiltonian_eq_integral (q : ScalarDomain 2) :
    periodOneKdVHamiltonian q=∫ x in (0:ℝ)..1,
      (1/2:ℂ)*(deriv (fun y : ℝ => periodOneSobolevSynthesis q (y : AddCircle (2:ℝ))) x)^2+
        (periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))^3 := by
  have hp : Function.Periodic (fun x : ℝ => ((periodOneSobolevSynthesis q)^3) (x : AddCircle (2:ℝ))) 1 := by
    intro x
    dsimp only [ContinuousMap.pow_apply]
    exact congrArg (fun v : ℂ => v^3) (periodOneSobolevSynthesis_periodic q x)
  rw [periodOneKdVHamiltonian,periodOneSobolevKinetic_eq_integral,periodOneCircleMean_eq_integral _ hp]
  rw [← intervalIntegral.integral_const_mul]
  have hk : IntervalIntegrable (fun x : ℝ => (1/2:ℂ)*
      (deriv (fun y : ℝ => periodOneSobolevSynthesis q (y : AddCircle (2:ℝ))) x *
        deriv (fun y : ℝ => periodOneSobolevSynthesis q (y : AddCircle (2:ℝ))) x)) volume 0 1 :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_deriv_periodOneSobolevSynthesis q).integrable_mul
        (memLp_deriv_periodOneSobolevSynthesis q))).const_mul _
  have hc : IntervalIntegrable (fun x : ℝ => (periodOneSobolevSynthesis q (x : AddCircle (2:ℝ)))^3) volume 0 1 :=
    ((continuous_periodOneSobolevSynthesis q).pow 3).intervalIntegrable 0 1
  simp only [ContinuousMap.pow_apply]
  rw [← intervalIntegral.integral_add hk hc]
  apply intervalIntegral.integral_congr
  intro x _
  ring

/-- The bilinear kinetic form is symmetric even for arbitrary complex H1 data. -/
theorem periodOneSobolevKinetic_symm (q h : ScalarDomain 2) :
    periodOneSobolevKinetic (q,h)=periodOneSobolevKinetic (h,q) := by
  rw [periodOneSobolevKinetic_eq_integral,periodOneSobolevKinetic_eq_integral]
  apply intervalIntegral.integral_congr
  intro x _
  exact mul_comm _ _

/-- The actual first variation, before an integration-by-parts gradient
identification. It is valid on the entire H1 Banach domain. -/
theorem hasDerivAt_periodOneKdVHamiltonian (q h : ScalarDomain 2) :
    HasDerivAt (fun z : ℂ => periodOneKdVHamiltonian (q+z • h))
      (periodOneSobolevKinetic (q,h)+
        periodOneCircleMean (3*(periodOneSobolevSynthesis q)^2*periodOneSobolevSynthesis h)) 0 := by
  let B : ScalarDomain 2 →L[ℂ] ScalarDomain 2 →L[ℂ] ℂ :=
    Coeff.dualPairing.bilinearComp
      (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp periodOneDerivative) periodOneDerivative
  have he (a b : ScalarDomain 2) : B a b=periodOneSobolevKinetic (a,b) := rfl
  have hcurve : HasDerivAt (fun z : ℂ => q+z • h) h 0 := by
    simpa only [one_smul] using! ((hasDerivAt_id (0:ℂ)).smul_const h).const_add q
  have hk := (B.hasDerivAt_of_bilinear (fun _ => hcurve) (fun _ => hcurve)).const_mul (1/2:ℂ)
  simp only [zero_smul,add_zero,he,periodOneSobolevKinetic_symm h q] at hk
  have hs := periodOneSobolevSynthesis.hasFDerivAt.comp_hasDerivAt (0:ℂ) hcurve
  have hc := periodOneCircleMean.hasFDerivAt.comp_hasDerivAt (0:ℂ) (hs.pow 3)
  simp only [Function.comp_apply,zero_smul,add_zero,Nat.cast_ofNat,show 3-1=2 by norm_num] at hc
  have hv : (1/2:ℂ)*(periodOneSobolevKinetic (q,h)+periodOneSobolevKinetic (q,h))=
      periodOneSobolevKinetic (q,h) := by ring
  rw [hv] at hk
  simpa only [periodOneKdVHamiltonian] using! hk.add hc

end NLS.KdV
