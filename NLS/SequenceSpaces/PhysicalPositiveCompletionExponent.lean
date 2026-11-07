import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedExponent
import NLS.SequenceSpaces.PositiveDeletedProjection
import NLS.SequenceSpaces.Reflection

/-! # Real-linear completion of positive coefficients in every native lp norm -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS
namespace Coeff
variable (p : ℝ≥0∞) [Fact (1≤p)]

def physicalPositiveCompletion : Coeff p →L[ℝ] Coeff p :=
  (ContinuousLinearMap.id ℝ _+
    (starL' ℝ : Coeff p ≃L[ℝ] Coeff p).toContinuousLinearMap.comp
      (reflection.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)).comp
        ((positiveDeletedProjection p 0).restrictScalars ℝ)

@[simp] theorem physicalPositiveCompletion_apply (a : Coeff p) (n : ℤ) :
    physicalPositiveCompletion p a n=(if 0<n then a n else 0)+conj (if 0< -n then a (-n) else 0) := by
  change (positiveDeletedProjection p 0 a+star (reflection (positiveDeletedProjection p 0 a)) : Coeff p) n=_
  rw [lp.coeFn_add,Pi.add_apply,lp.star_apply,reflection_apply,
    positiveDeletedProjection_apply,positiveDeletedProjection_apply]
  have h1 : (0<n ∧ n≠0) ↔ 0<n := by omega
  have h2 : (0< -n ∧ -n≠0) ↔ 0< -n := by omega
  simp only [h1,h2,starRingEnd_apply]

end Coeff
namespace WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1≤p)]

def physicalPositiveLift : Coeff p →L[ℝ] WeightedCoeff w p :=
  ((weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
    (Coeff.physicalPositiveCompletion p)

@[simp] theorem physicalPositiveLift_apply (a : Coeff p) (n : ℤ) :
    (physicalPositiveLift w p a).val n=
      ((if 0<n then a n else 0)+conj (if 0< -n then a (-n) else 0))/(w n : ℂ) := by
  change ((weightEquiv w p).symm (Coeff.physicalPositiveCompletion p a)).val n=_
  change Coeff.physicalPositiveCompletion p a n/(w n : ℂ)=_
  rw [Coeff.physicalPositiveCompletion_apply]

theorem physicalPositiveLift_real (hw : ∀ n : ℤ, w (-n)=w n) (a : Coeff p) :
    physicalPositiveLift w p a∈physicalRealMeanZeroWeightedExponent w p := by
  constructor
  · intro n
    simp only [physicalPositiveLift_apply,hw,neg_neg,map_div₀,map_add,conj_conj,conj_ofReal]
    congr 1
    exact add_comm _ _
  · simp only [physicalPositiveLift_apply,neg_zero,lt_self_iff_false,↓reduceIte,map_zero,
      add_zero,zero_div]

/-- Complete positive normalized coordinates to the ORIGINAL physical
real mean-zero weighted lp space by a bounded real-linear map. -/
def physicalPositiveRealLift (hw : ∀ n : ℤ, w (-n)=w n) :
    Coeff p →L[ℝ] physicalRealMeanZeroWeightedExponent w p :=
  (physicalPositiveLift w p).codRestrict _ (physicalPositiveLift_real w p hw)

@[simp] theorem physicalPositiveRealLift_apply (hw : ∀ n : ℤ, w (-n)=w n)
    (a : Coeff p) (n : ℤ) :
    (physicalPositiveRealLift w p hw a).val.val n=
      ((if 0<n then a n else 0)+conj (if 0< -n then a (-n) else 0))/(w n : ℂ) :=
  physicalPositiveLift_apply w p a n

end WeightedCoeff
end NLS
