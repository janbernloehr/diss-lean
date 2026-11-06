import NLS.Articles.KdVKdV2Frequencies.ActualSignedPrincipalSymbol
import NLS.SequenceSpaces.MeanZeroWeightedCoordinates

/-! # The ACTUAL signed principal is an equivalence in the native mean-zero charts -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- The exact actual signed principal in the literal native source and
target mean-zero charts, with no change of weights or physical symbols. -/
def actualMeanZeroFourierPrincipal (D : RoughAbelianFourierData) (e : ℤ → Bool)
    (t : ℝ) (ht : 0≤t) (q : WeightedCoeff (Weight.sobolev (t-1)) 2) :
    DeletedCoeff 2 0 →L[ℂ] DeletedCoeff 2 0 :=
  (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (t-1/2))).comp
    ((actualSignedFourierPrincipal D e t ht q).comp
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1))))

/-- At EVERY eligible real native base and EVERY native order the SAME
actual mean-zero signed principal is a bounded equivalence. Its inverse
uses the actual full-symbol/root/phase reciprocal and free Miura map. -/
theorem exists_actualMeanZeroFourierPrincipal_equiv
    (D : RoughAbelianFourierData) (e : ℤ → Bool) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : periodOneSobolevImageInclusion t ht q∈ball (0 : PeriodOneHminusOne) D.radius)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q)) :
    ∃ E : DeletedCoeff 2 0 ≃L[ℂ] DeletedCoeff 2 0,
      E.toContinuousLinearMap=actualMeanZeroFourierPrincipal D e t ht q := by
  obtain ⟨b,ha,hb,hab⟩ := exists_actualPositivePrincipalSymbol_reciprocal D e _ hq hqr
  let a := actualPositivePrincipalSymbol D e (periodOneSobolevImageInclusion t ht q)
  let M := Coeff.completedPositiveMultiplierEquiv a b ha hb hab
  let E := (periodOneMeanZeroFreeFourierEquiv t ht).trans M
  refine ⟨E,?_⟩
  rw [actualMeanZeroFourierPrincipal,actualSignedFourierPrincipal_eq_multiplier D e t ht q hqr]
  apply ContinuousLinearMap.ext
  intro h
  apply Subtype.ext
  ext n
  by_cases hn : n=0
  · subst n
    exact (E h).property.trans ((WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (t-1/2))) _).property.symm
  · change (Coeff.completedPositiveSymbol a n)*(periodOneMeanZeroFreeFourierEquiv t ht h).val n=
      Coeff.deleteCoordinate 0
        ((WeightedCoeff.weightIsometry (Weight.sobolev (t-1/2)) 2)
          ((WeightedCoeff.weightIsometry (Weight.sobolev (t-1/2)) 2).symm
            (Coeff.holderProduct (q := 2) (Coeff.completedPositiveSymbol a)
              (periodOneNativeFreeFourierEquiv t ht
                (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (t-1)) h))))) n
    rw [LinearIsometryEquiv.apply_symm_apply,Coeff.deleteCoordinate_apply_other 0 n hn]
    rfl

end NLS.Articles.KdVKdV2Frequencies
