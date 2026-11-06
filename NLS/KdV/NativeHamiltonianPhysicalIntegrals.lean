import NLS.KdV.NativeHamiltonianPolynomials
import NLS.KdV.RiccatiEnergy
import NLS.Fourier.SobolevContinuousJetDerivative
import NLS.Fourier.PeriodOneFourierUniqueness

/-! # Exact physical integrals of the native KdV Hamiltonians

All endpoint identities hold for arbitrary original H1 and H2 coefficients.
The continuous representative has its actual classical derivatives; the
highest derivative is square integrable. No smoothness premise is imposed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

/-- The article's actual complexified second KdV Hamiltonian on one
physical period, with the exact coefficients 1/2, 5 and 5/2. -/
def classicalKdV2Hamiltonian (u : ℝ → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, (deriv (deriv u) x)^2/2+5*u x*(deriv u x)^2+(5/2 : ℂ)*(u x)^4

theorem intervalIntegrable_topJetPhysical_sq (s : ℕ) (hs : 1≤s) (a : ScalarSobolev s) :
    IntervalIntegrable (fun x => (sobolevTopJetPhysical s hs a x)^2) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
  simpa only [pow_two,Pi.mul_apply] using! (memLp_sobolevTopJetPhysical s hs a).integrable_mul
    (memLp_sobolevTopJetPhysical s hs a)

/-- The native H1 polynomial is EXACTLY the physical KdV integral on the
FULL H1 domain, using the actual classical derivative almost everywhere. -/
theorem nativeKdVHamiltonian_eq_classical (a : ScalarSobolev 1) :
    nativeKdVHamiltonian a=classicalHamiltonian
      (fun x : ℝ => hierarchySobolevJetContinuous 1 0 (by omega) a (x : AddCircle (2 : ℝ))) := by
  let u := fun x : ℝ => hierarchySobolevJetContinuous 1 0 (by omega) a (x : AddCircle (2 : ℝ))
  have he : sobolevTopJetPhysical 1 (by omega) a=deriv u := by
    simpa only [iteratedDeriv_one] using sobolevTopJetPhysical_eq_iteratedDeriv 1 (by omega) a
  have hK : IntervalIntegrable (fun x => (deriv u x)^2) volume 0 1 := by
    simpa only [he] using intervalIntegrable_topJetPhysical_sq 1 (by omega) a
  have hu : Continuous u := (hierarchySobolevJetContinuous 1 0 (by omega) a).continuous.comp continuous_quotient_mk'
  have hp := hierarchySobolevJetContinuous_periodic 1 0 (by omega) a
  have hM := periodOneCircleMean_eq_integral ((hierarchySobolevJetContinuous 1 0 (by omega) a)^3) (by intro x; simpa only [ContinuousMap.pow_apply] using! congrArg (fun z : ℂ => z^3) (hp x))
  rw [nativeKdVHamiltonian,nativeTopJetSquare_eq_integral 1 (by omega),he,hM]
  change (1/2 : ℂ)*(∫ x in (0 : ℝ)..1, (deriv u x)^2)+(∫ x in (0 : ℝ)..1, (u x)^3)=_
  change (1/2 : ℂ)*(∫ x in (0 : ℝ)..1, (deriv u x)^2)+(∫ x in (0 : ℝ)..1, (u x)^3)=classicalHamiltonian u
  rw [classicalHamiltonian,intervalIntegral.integral_add,intervalIntegral.integral_div]
  · ring
  · exact hK.div_const 2
  · exact (hu.pow 3).intervalIntegrable 0 1

/-- The native H2 polynomial is EXACTLY the physical KdV2 integral on
the FULL H2 domain, with its actual first and second derivatives. -/
theorem nativeKdV2Hamiltonian_eq_classical (a : ScalarSobolev 2) :
    nativeKdV2Hamiltonian a=classicalKdV2Hamiltonian
      (fun x : ℝ => hierarchySobolevJetContinuous 2 0 (by omega) a (x : AddCircle (2 : ℝ))) := by
  let U := hierarchySobolevJetContinuous 2 0 (by omega) a
  let V := hierarchySobolevJetContinuous 2 1 (by omega) a
  let u := fun x : ℝ => U (x : AddCircle (2 : ℝ))
  have hd : deriv u=(fun x : ℝ => V (x : AddCircle (2 : ℝ))) :=
    funext (fun x => (hasDerivAt_hierarchySobolevJetContinuous 2 0 (by omega) a x).deriv)
  have he : sobolevTopJetPhysical 2 (by omega) a=deriv (deriv u) := by
    simpa only [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] using!
      sobolevTopJetPhysical_eq_iteratedDeriv 2 (by omega) a
  have hK : IntervalIntegrable (fun x => (deriv (deriv u) x)^2) volume 0 1 := by
    simpa only [he] using intervalIntegrable_topJetPhysical_sq 2 (by omega) a
  have hu : Continuous u := U.continuous.comp continuous_quotient_mk'
  have hv : Continuous (deriv u) := by rw [hd]; exact V.continuous.comp continuous_quotient_mk'
  have hp := hierarchySobolevJetContinuous_periodic 2 0 (by omega) a
  have hvp := hierarchySobolevJetContinuous_periodic 2 1 (by omega) a
  have hM := periodOneCircleMean_eq_integral (U*V^2) (by intro x; simpa only [ContinuousMap.mul_apply,ContinuousMap.pow_apply] using! congrArg₂ (fun z w : ℂ => z*w^2) (hp x) (hvp x))
  have hQ := periodOneCircleMean_eq_integral (U^4) (by intro x; simpa only [ContinuousMap.pow_apply] using! congrArg (fun z : ℂ => z^4) (hp x))
  rw [nativeKdV2Hamiltonian,nativeTopJetSquare_eq_integral 2 (by omega),he,hM,hQ]
  change (1/2 : ℂ)*(∫ x in (0 : ℝ)..1, (deriv (deriv u) x)^2)+
    5*(∫ x in (0 : ℝ)..1, u x*(V (x : AddCircle (2 : ℝ)))^2)+
    (5/2 : ℂ)*(∫ x in (0 : ℝ)..1, (u x)^4)=_
  have hdx (x : ℝ) : V (x : AddCircle (2 : ℝ))=deriv u x := (congrFun hd x).symm
  simp_rw [hdx]
  change _=classicalKdV2Hamiltonian u
  rw [classicalKdV2Hamiltonian]
  have hI : IntervalIntegrable (fun x => (5 : ℂ)*u x*(deriv u x)^2) volume 0 1 :=
    ((continuous_const.mul hu).mul (hv.pow 2)).intervalIntegrable 0 1
  have hJ : IntervalIntegrable (fun x => (5/2 : ℂ)*(u x)^4) volume 0 1 :=
    (continuous_const.mul (hu.pow 4)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add ((hK.div_const 2).add hI) hJ,
    intervalIntegral.integral_add (hK.div_const 2) hI,intervalIntegral.integral_div]
  simp_rw [mul_assoc (5 : ℂ),intervalIntegral.integral_const_mul]
  ring

private theorem zeroJet_eq_of_coefficients (s : ℕ) (hs : 1≤s) (a : ScalarSobolev s)
    (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1)
    (ha : ∀ n, a.val n=periodOneCoefficient f n) :
    (fun x : ℝ => hierarchySobolevJetContinuous s 0 (by omega) a (x : AddCircle (2 : ℝ)))=f := by
  change (fun x : ℝ => periodOneSobolevSynthesis (hierarchySobolevToScalarDomain s hs a)
    (x : AddCircle (2 : ℝ)))=f
  exact periodOneSobolevSynthesis_eq_of_coefficients _ f hf hp
    (fun n => (hierarchySobolevToScalarDomain_apply s hs a n).trans (ha n))

/-- Exact comparison with ANY continuous physical period-one source
whose ORIGINAL coefficients lie in H1; no smoothness is required. -/
theorem nativeKdVHamiltonian_eq_of_coefficients (a : ScalarSobolev 1)
    (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1)
    (ha : ∀ n, a.val n=periodOneCoefficient f n) : nativeKdVHamiltonian a=classicalHamiltonian f := by
  rw [nativeKdVHamiltonian_eq_classical,zeroJet_eq_of_coefficients 1 (by omega) a f hf hp ha]

/-- Exact comparison with ANY continuous physical period-one source
whose ORIGINAL coefficients lie in H2; no smoothness is required. -/
theorem nativeKdV2Hamiltonian_eq_of_coefficients (a : ScalarSobolev 2)
    (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1)
    (ha : ∀ n, a.val n=periodOneCoefficient f n) : nativeKdV2Hamiltonian a=classicalKdV2Hamiltonian f := by
  rw [nativeKdV2Hamiltonian_eq_classical,zeroJet_eq_of_coefficients 2 (by omega) a f hf hp ha]

end NLS.KdV
