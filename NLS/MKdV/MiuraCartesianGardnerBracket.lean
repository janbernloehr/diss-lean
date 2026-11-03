import NLS.MKdV.MiuraCartesianGardnerCotangent
import NLS.Poisson.L2GardnerSkew

/-! # Analytic actual Cartesian Gardner brackets on original H1

The bounded cotangent formula gives a complex analytic H1 extension of
every Cartesian-Cartesian bracket. On physical sources it is the literal
Gardner bracket and is skew symmetric, without a gap hypothesis.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem analyticAt_miuraCartesianGeneratorCotangent (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m) :
    AnalyticAt ℂ (fun b : ScalarDomain 2 => miuraCartesianGeneratorCotangent b m) a := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  have hf := analyticAt_miuraL2CartesianCoordinates _ har m hm
  have hd := hf.fderiv.comp (scalarInclusion.analyticAt a)
  have hdd := hf.fderiv.fderiv.comp (scalarInclusion.analyticAt a)
  let T : (Coeff 2 →L[ℂ] Coeff 2 →L[ℂ] (ℂ × ℂ)) →L[ℂ]
      (Coeff 2 →L[ℂ] Coeff 2 →L[ℂ] (ℂ × ℂ)) := (ContinuousLinearMap.flipₗᵢ ℂ (Coeff 2) (Coeff 2) (ℂ × ℂ)).toContinuousLinearEquiv.toContinuousLinearMap
  have hT := @ContinuousLinearMap.analyticAt ℂ inferInstance
    (Coeff 2 →L[ℂ] Coeff 2 →L[ℂ] (ℂ × ℂ)) inferInstance inferInstance
    (Coeff 2 →L[ℂ] Coeff 2 →L[ℂ] (ℂ × ℂ)) inferInstance inferInstance T
    (fderiv ℂ (fderiv ℂ (miuraL2CartesianCoordinates m)) (scalarInclusion a))
  have hb := ((ContinuousLinearMap.apply (E := Coeff 2) ℂ (Coeff 2 →L[ℂ] (ℂ × ℂ))).analyticAt_bilinear _).comp₂
    (periodOneDerivative.analyticAt a) (hT.comp (f := fun b : ScalarDomain 2 =>
      fderiv ℂ (fderiv ℂ (miuraL2CartesianCoordinates m)) (scalarInclusion b)) hdd)
  have hr := ((ContinuousLinearMap.compL ℂ (Coeff 2) (ℂ × ℂ) (ℂ × ℂ)
    (miuraCartesianSpatialGenerator m)).analyticAt _).comp hd
  exact hr.sub hb

def miuraCartesianGardnerBracketExtension (m n : ℕ)
    (P Q : (ℂ × ℂ) →L[ℂ] ℂ) (a : ScalarDomain 2) : ℂ :=
  (fderiv ℂ (miuraCartesianObservable m P) (scalarInclusion a))
    (-Coeff.reflection (Coeff.hilbertCotangentCoefficients (Q.comp (miuraCartesianGeneratorCotangent a n))))

theorem analyticAt_miuraCartesianGardnerBracketExtension (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (P Q : (ℂ × ℂ) →L[ℂ] ℂ) :
    AnalyticAt ℂ (miuraCartesianGardnerBracketExtension m n P Q) a := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  have hF : AnalyticAt ℂ (miuraCartesianObservable m P) (scalarInclusion a) :=
    (P.analyticAt _).comp (analyticAt_miuraL2CartesianCoordinates _ har m hm)
  have hdf := hF.fderiv.comp (scalarInclusion.analyticAt a)
  have hL := ((ContinuousLinearMap.compL ℂ (Coeff 2) (ℂ × ℂ) ℂ Q).analyticAt _).comp
    (analyticAt_miuraCartesianGeneratorCotangent a ha n hn)
  have hg := (((Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
    ((Coeff.hilbertCotangentCoefficients.analyticAt _).comp hL))).neg
  exact ((ContinuousLinearMap.apply (E := Coeff 2) ℂ ℂ).analyticAt_bilinear _).comp₂ hg hdf

theorem miuraCartesianGardnerBracketExtension_eq_actual (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hn : 1 ≤ n)
    (P Q : (ℂ × ℂ) →L[ℂ] ℂ) :
    miuraCartesianGardnerBracketExtension m n P Q a =
      l2GardnerBracket (miuraCartesianObservable m P) (miuraCartesianObservable n Q) (scalarInclusion a) := by
  rw [l2GardnerBracket,miuraCartesianObservable_GardnerDirection a ha n hn Q]
  rfl

theorem miuraCartesianGardnerBracket_antisymm (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (P Q : (ℂ × ℂ) →L[ℂ] ℂ) :
    l2GardnerBracket (miuraCartesianObservable m P) (miuraCartesianObservable n Q) (scalarInclusion a) =
      -l2GardnerBracket (miuraCartesianObservable n Q) (miuraCartesianObservable m P) (scalarInclusion a) :=
  l2GardnerBracket_antisymm_of_memlp _ _ _
    (miuraCartesianObservable_Gardner_memlp a ha m hm P)
    (miuraCartesianObservable_Gardner_memlp a ha n hn Q)

theorem miuraCartesianGardnerBracket_self (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (P : (ℂ × ℂ) →L[ℂ] ℂ) :
    l2GardnerBracket (miuraCartesianObservable m P) (miuraCartesianObservable m P) (scalarInclusion a) = 0 :=
  l2GardnerBracket_self_eq_zero_of_memlp _ _ (miuraCartesianObservable_Gardner_memlp a ha m hm P)

end NLS.MKdV
