import NLS.ZakharovShabat.SobolevClassicalFreeUniform
import NLS.ZakharovShabat.ContinuousSourceAntiDiscriminantGradient
import NLS.ZakharovShabat.SourceBoundaryRootDifferential
import NLS.ZakharovShabat.HilbertDiscriminant

/-! # Exact source and classical spectral compatibility

Continuous periodic representatives with matching original Fourier coefficients identify the actual source functions and canonical boundary roots.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Matching unit-period coefficients give the actual continuous physical
representative of the original Sobolev source. -/
theorem physicalBase_higherSobolev_eq_classicalPotentialOfFunctions
    (s : ℕ) (hs : 1 ≤ s) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : Continuous a) (hb : Continuous b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hca : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hcb : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    physicalBase (periodOnePotential (higherSobolevSourceInclusion s ab))
      =ᵐ[volume.restrict (Ioc 0 1)] extend (classicalPotentialOfFunctions a b ha hb) := by
  let c : Domain 2 :=
    (Coeff.periodDoubleSobolev (hierarchySobolevToScalarDomain s hs ab.1),
     Coeff.periodDoubleSobolev (hierarchySobolevToScalarDomain s hs ab.2))
  have he : periodOnePotential (higherSobolevSourceInclusion s ab) = domainInclusion c := by
    rw [← sobolevSourceInclusion_higherSobolevToH1 s hs ab]
    have hf : (sobolevSourceInclusion (higherSobolevToH1 s hs ab)).fst =
        scalarInclusion (hierarchySobolevToScalarDomain s hs ab.1) := by
      ext n
      simp [higherSobolevToH1]
    have hg : (sobolevSourceInclusion (higherSobolevToH1 s hs ab)).snd =
        scalarInclusion (hierarchySobolevToScalarDomain s hs ab.2) := by
      ext n
      simp [higherSobolevToH1]
    rw [periodOnePotential_apply,domainInclusion_apply,hf,hg]
    apply Prod.ext <;> ext n <;>
      simp only [c,scalarInclusion_apply,Coeff.periodDoubleSobolev_apply]
  rw [classicalPotentialOfFunctions_eq_higherSobolev s hs ab a b ha hb hpa hpb hca hcb,he]
  exact physicalBase_eq_extend_physicalDomainCurve c

/-- All three actual source spectral functions agree with the classical
functions of any matching continuous periodic representative. -/
theorem higherSobolev_spectral_functions_eq_classical
    (s : ℕ) (hs : 1 ≤ s) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : Continuous a) (hb : Continuous b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hca : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hcb : ∀ j, ab.2.val j = periodOneCoefficient b j) (z : ℂ) :
    canonicalDiscriminant (by norm_num)
      (periodOnePotential (higherSobolevSourceInclusion s ab)) z =
      classicalDiscriminant (classicalPotentialOfFunctions a b ha hb) z ∧
    sourceAntiDiscriminantCandidate (by norm_num) (by norm_num)
      (higherSobolevSourceInclusion s ab) z =
      classicalAntiDiscriminant (classicalPotentialOfFunctions a b ha hb) z ∧
    ∀ θ : BoundaryCondition,
      periodOneBoundaryCharacteristic (by norm_num) (by norm_num) θ
        (higherSobolevSourceInclusion s ab) z =
        classicalSeparatedCharacteristic θ (classicalPotentialOfFunctions a b ha hb) z := by
  have hΦ := physicalBase_higherSobolev_eq_classicalPotentialOfFunctions s hs ab a b ha hb hpa hpb hca hcb
  exact ⟨canonicalDiscriminant_eq_classical _ (periodOnePotential_mem _) _ hΦ z,
    sourceAntiDiscriminantCandidate_eq_classical_of_continuous _ _ hΦ z,
    fun θ => periodOneBoundaryCharacteristic_eq_classical_of_continuous θ _ _ hΦ z⟩

/-- Every original canonical boundary root is a zero of the matching
classical characteristic, with its original signed label. -/
theorem classicalSeparatedCharacteristic_higherSobolev_canonicalRoot_eq_zero
    (s : ℕ) (hs : 1 ≤ s) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : Continuous a) (hb : Continuous b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hca : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hcb : ∀ j, ab.2.val j = periodOneCoefficient b j) (θ : BoundaryCondition) (n : ℤ) :
    classicalSeparatedCharacteristic θ (classicalPotentialOfFunctions a b ha hb)
      (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
        (higherSobolevSourceInclusion s ab) n) = 0 := by
  rw [← (higherSobolev_spectral_functions_eq_classical s hs ab a b ha hb hpa hpb hca hcb _).2.2 θ]
  exact periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero (by norm_num) (by norm_num) θ _ n

end NLS.ZakharovShabat
