import NLS.ZakharovShabat.SobolevHamiltonianConservation
import NLS.ZakharovShabat.LocalClassicalNLSMass
import NLS.Fourier.PeriodOneSynthesisAlgebra
import NLS.SequenceSpaces.ConjugateReflection

/-! # Scalar physical energy conservation in the H¹ topology -/
noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ComplexConjugate
namespace NLS.ZakharovShabat

/-- Physical conjugation is a bounded real-linear map on the scalar H¹ space. -/
def sobolevConjugateCLM : ScalarDomain 2 →L[ℝ] ScalarDomain 2 :=
  LinearMap.mkContinuous
    { toFun := WeightedCoeff.conjugateReflection (Weight.sobolev 1) (by intro n; simp)
      map_add' := by
        intro a b
        apply Subtype.ext
        funext n
        simp only [WeightedCoeff.conjugateReflection_apply,WeightedCoeff.add_val,map_add]
      map_smul' := by
        intro c a
        apply Subtype.ext
        funext n
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul c a,← Complex.coe_smul c
          (WeightedCoeff.conjugateReflection (Weight.sobolev 1) _ a)]
        simp only [WeightedCoeff.conjugateReflection_apply,WeightedCoeff.smul_val,map_mul,conj_ofReal] }
    1 (by
      intro a
      change ‖WeightedCoeff.conjugateReflection (Weight.sobolev 1) (by intro n; simp) a‖ ≤ 1*‖a‖
      rw [WeightedCoeff.norm_conjugateReflection,one_mul])

@[simp] theorem sobolevConjugateCLM_apply (a : ScalarDomain 2) (n : ℤ) :
    (sobolevConjugateCLM a).val n = conj (a.val (-n)) :=
  WeightedCoeff.conjugateReflection_apply _ (by intro n; simp) _ _

/-- Sobolev conjugate reflection is actual pointwise physical conjugation. -/
theorem periodOneSobolevSynthesis_conjugate (a : ScalarDomain 2) (x : ℝ) :
    periodOneSobolevSynthesis (sobolevConjugateCLM a) (x : AddCircle (2 : ℝ)) =
      conj (periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))) := by
  have he : WeightedCoeff.sobolevToL1CLM 2 (by simp) (sobolevConjugateCLM a) =
      star (Coeff.reflection (WeightedCoeff.sobolevToL1CLM 2 (by simp) a)) := by
    ext n
    simp [WeightedCoeff.sobolevToL1CLM_apply,sobolevConjugateCLM_apply,Coeff.reflection_apply]
  simp only [periodOneSobolevSynthesis_apply,he,periodOneSynthesis_conjugateReflection]

/-- A scalar H¹ field and its physical complex conjugate. -/
def sobolevRealPairCLM : ScalarDomain 2 →L[ℝ] ScalarDomain 2 × ScalarDomain 2 :=
  (ContinuousLinearMap.id ℝ _).prod sobolevConjugateCLM

/-- The defocusing physical energy, as the existing Hamiltonian on the real pair. -/
def scalarSobolevEnergy (a : ScalarDomain 2) : ℂ :=
  periodOneSobolevHamiltonian (sobolevRealPairCLM a)

theorem continuous_scalarSobolevEnergy : Continuous scalarSobolevEnergy :=
  continuous_periodOneSobolevHamiltonian.comp sobolevRealPairCLM.continuous

/-- The scalar energy is the literal unit-period integral of kinetic and
nonnegative quartic energy. -/
theorem scalarSobolevEnergy_eq_integral (a : ScalarDomain 2) :
    scalarSobolevEnergy a = ∫ x in (0 : ℝ)..1,
      ((‖deriv (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ))) x‖^2 +
        ‖periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))‖^4 : ℝ) : ℂ) := by
  change periodOneSobolevHamiltonian (a,sobolevConjugateCLM a) = _
  rw [periodOneSobolevHamiltonian_eq_integral]
  have he : (fun x : ℝ => periodOneSobolevSynthesis (sobolevConjugateCLM a) (x : AddCircle (2 : ℝ))) =
      fun x : ℝ => conj (periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))) :=
    funext (periodOneSobolevSynthesis_conjugate a)
  rw [he]
  have hd : deriv (fun x : ℝ => conj (periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)))) =
      fun x : ℝ => conj (deriv (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ))) x) := deriv.star'
  rw [hd]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [periodOneSobolevSynthesis_conjugate,← mul_pow,Complex.mul_conj',Complex.mul_conj']
  push_cast
  ring

/-- The physical energy is real and equals the usual real-valued integral. -/
theorem scalarSobolevEnergy_eq_real_integral (a : ScalarDomain 2) :
    scalarSobolevEnergy a = ((∫ x in (0 : ℝ)..1,
      ‖deriv (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ))) x‖^2 +
        ‖periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))‖^4 : ℝ) : ℂ) := by
  rw [scalarSobolevEnergy_eq_integral,intervalIntegral.integral_ofReal]

/-- The physical scalar NLS equation annihilates the real-pair energy derivative. -/
theorem energy_variation_zero_of_scalar_NLS (a v : ScalarDomain 2)
    (ha : ContDiff ℝ ∞ (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))))
    (he : ∀ x : ℝ, periodOneSobolevSynthesis v (x : AddCircle (2 : ℝ)) =
      scalarClassicalNLSVectorField (fun y : ℝ => periodOneSobolevSynthesis a (y : AddCircle (2 : ℝ))) x) :
    (fderiv ℂ periodOneSobolevHamiltonian (sobolevRealPairCLM a)) (sobolevRealPairCLM v) = 0 := by
  have hc : (fun x : ℝ => periodOneSobolevSynthesis (sobolevConjugateCLM a) (x : AddCircle (2 : ℝ))) =
      fun x : ℝ => conj (periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))) :=
    funext (periodOneSobolevSynthesis_conjugate a)
  apply fderiv_periodOneSobolevHamiltonian_eq_zero_of_field a (sobolevConjugateCLM a) v
    (sobolevConjugateCLM v) ha (by rw [hc]; exact Complex.conjCLE.contDiff.comp ha)
  intro x
  rw [hc]
  apply Prod.ext
  · exact (he x).trans (congrFun (scalarClassicalNLSVectorField_eq _) x)
  · rw [periodOneSobolevSynthesis_conjugate,he x,scalarClassicalNLSVectorField_eq,
      classicalNLSVectorField_real]

/-- Any strong local H¹ realization of a classical scalar solution conserves
its actual physical energy, including the two time endpoints. -/
theorem scalarSobolevEnergy_eq_of_local_classical
    {a b : ℝ} (u : ℝ → ScalarDomain 2)
    (hc : ContinuousOn u (Icc a b))
    (hd : ∀ time ∈ Ioo a b, DifferentiableAt ℝ u time)
    (hu : IsClassicalNLSTrajectoryOn a b (fun time => periodOneSobolevSynthesis (u time)))
    {time initial : ℝ} (ht : time ∈ Icc a b) (hi : initial ∈ Icc a b) :
    scalarSobolevEnergy (u time) = scalarSobolevEnergy (u initial) := by
  apply FunctionalAnalysis.eq_of_hasDerivAt_zero_Icc
    (continuous_scalarSobolevEnergy.comp_continuousOn hc) _ ht hi
  intro r hr
  have hp := sobolevRealPairCLM.hasFDerivAt.comp_hasDerivAt r (hd r hr).hasDerivAt
  have hh := ((analyticAt_periodOneSobolevHamiltonian (sobolevRealPairCLM (u r))).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r hp
  apply hh.congr_deriv
  apply energy_variation_zero_of_scalar_NLS _ _ (hu.spatial_smooth r ⟨hr.1.le,hr.2.le⟩)
  intro x
  have hv := (periodOneSobolevSynthesis.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r (hd r hr).hasDerivAt
  have he := hu.equation r hr x
  have hv' : HasDerivAt (fun time => periodOneSobolevSynthesis (u time))
      (periodOneSobolevSynthesis (deriv u r)) r := hv
  rw [hv'.deriv] at he
  exact he

end NLS.ZakharovShabat
