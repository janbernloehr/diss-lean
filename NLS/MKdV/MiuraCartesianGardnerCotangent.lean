import NLS.MKdV.MiuraCartesianTranslationGenerator
import NLS.ComplexAnalysis.TranslationCovariantCotangent
import NLS.Poisson.L2GardnerCotangentDomain
import NLS.SequenceSpaces.PhysicalRealCoefficients

/-! # Actual Gardner fields of the Cartesian observables

The differentiated physical translation identity proves the generator
domain of each actual Cartesian gradient. Its spatial derivative has a
literal L2 representative, also at every closed selected gap.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraCartesianGeneratorCotangent (a : ScalarDomain 2) (m : ℕ) :
    Coeff 2 →L[ℂ] (ℂ × ℂ) :=
  (miuraCartesianSpatialGenerator m).comp
    (fderiv ℂ (miuraL2CartesianCoordinates m) (scalarInclusion a))-
      (fderiv ℂ (fderiv ℂ (miuraL2CartesianCoordinates m)) (scalarInclusion a)).flip (periodOneDerivative a)

theorem miuraCartesian_generator_cotangent_identity (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m) :
    (fderiv ℂ (miuraL2CartesianCoordinates m) (scalarInclusion a)).comp periodOneDerivative =
      (miuraCartesianGeneratorCotangent a m).comp scalarInclusion := by
  let V := WeightedCoeff.physicalRealSubmodule (Weight.sobolev 1) 2
  have hw : ∀ k : ℤ, Weight.sobolev 1 (-k) = Weight.sobolev 1 k := by intro k; simp
  have hspan (h : ScalarDomain 2) : ∃ x y : V, h = x.val+I • y.val :=
    ⟨WeightedCoeff.physicalRealPart (Weight.sobolev 1) hw h,
      WeightedCoeff.physicalRealPart (Weight.sobolev 1) hw ((-I) • h),
        WeightedCoeff.physicalRealPart_complex_decomp _ hw h⟩
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  exact NLS.ComplexAnalysis.fderiv_generator_eq_of_real_covariance V hspan
    scalarInclusion periodOneDerivative (miuraCartesianSpatialGenerator m) (miuraL2CartesianCoordinates m)
    ⟨a,ha⟩ (analyticAt_miuraL2CartesianCoordinates _ har m hm)
    (fun b => fderiv_miuraCartesian_spatialDerivative b.val b.property m hm)

def miuraCartesianObservable (m : ℕ) (P : (ℂ × ℂ) →L[ℂ] ℂ) (b : Coeff 2) : ℂ :=
  P (miuraL2CartesianCoordinates m b)

theorem fderiv_miuraCartesianObservable (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (P : (ℂ × ℂ) →L[ℂ] ℂ) :
    fderiv ℂ (miuraCartesianObservable m P) (scalarInclusion a) =
      P.comp (fderiv ℂ (miuraL2CartesianCoordinates m) (scalarInclusion a)) := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  exact (P.hasFDerivAt.comp _
    (analyticAt_miuraL2CartesianCoordinates _ har m hm).differentiableAt.hasFDerivAt).fderiv

theorem miuraCartesianObservable_generator_cotangent_identity (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (P : (ℂ × ℂ) →L[ℂ] ℂ) :
    (fderiv ℂ (miuraCartesianObservable m P) (scalarInclusion a)).comp periodOneDerivative =
      (P.comp (miuraCartesianGeneratorCotangent a m)).comp scalarInclusion := by
  rw [fderiv_miuraCartesianObservable a ha m hm P,ContinuousLinearMap.comp_assoc,
    miuraCartesian_generator_cotangent_identity a ha m hm,← ContinuousLinearMap.comp_assoc]

theorem miuraCartesianObservable_Gardner_memlp (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (P : (ℂ × ℂ) →L[ℂ] ℂ) :
    Memℓp (fun j : ℤ => 2*I*(Real.pi : ℂ)*j*
      l2ScalarGradient (miuraCartesianObservable m P) (scalarInclusion a) j) 2 := by
  simp only [l2ScalarGradient_apply]
  exact memlp_spatialGradient_of_cotangent_extension _ _
    (miuraCartesianObservable_generator_cotangent_identity a ha m hm P)

theorem miuraCartesianObservable_GardnerDirection (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (P : (ℂ × ℂ) →L[ℂ] ℂ) :
    l2GardnerDirection (miuraCartesianObservable m P) (scalarInclusion a) =
      -Coeff.reflection (Coeff.hilbertCotangentCoefficients (P.comp (miuraCartesianGeneratorCotangent a m))) :=
  l2GardnerDirection_eq_of_cotangent_extension _ _ _
    (miuraCartesianObservable_generator_cotangent_identity a ha m hm P)

theorem miuraCartesianObservable_Gardner_distribution (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (P : (ℂ × ℂ) →L[ℂ] ℂ) :
    TemperedDistribution.derivCLM ℂ
        (NLS.Fourier.periodOneL2Distribution (l2ScalarGradient (miuraCartesianObservable m P) (scalarInclusion a))) =
      NLS.Fourier.periodOneL2Distribution
        (l2GardnerDirection (miuraCartesianObservable m P) (scalarInclusion a)) :=
  l2GardnerDirection_distribution_of_cotangent_extension _ _ _
    (miuraCartesianObservable_generator_cotangent_identity a ha m hm P)

end NLS.MKdV
