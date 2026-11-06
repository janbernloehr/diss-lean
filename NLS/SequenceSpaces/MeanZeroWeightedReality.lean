import NLS.SequenceSpaces.MeanZeroSobolevInclusion
import NLS.SequenceSpaces.DeletedRealConjugation
import NLS.SequenceSpaces.WeightedSourceSignedCompletion

/-! # Exact real-form transport through mean-zero weighted charts -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
namespace NLS

theorem isometry_deletedL2Conjugation : Isometry deletedL2Conjugation := by
  apply Isometry.of_dist_eq
  intro a b
  rw [dist_eq_norm,dist_eq_norm]
  change ‖periodOneL2Conjugation a.val-periodOneL2Conjugation b.val‖ = ‖a.val-b.val‖
  rw [←periodOneL2Conjugation_sub,norm_periodOneL2Conjugation]

namespace WeightedCoeff

theorem meanZeroWeightedLift_conjugation (w : Weight) (hw : ∀ j, w (-j) = w j)
    (a : DeletedCoeff 2 0) :
    meanZeroWeightedLiftCLM w (deletedL2Conjugation a) =
      conjugateReflection w hw (meanZeroWeightedLiftCLM w a) := by
  apply (weightIsometry w 2).injective
  rw [←weightIsometry_conjugateReflection w hw]
  change (weightIsometry w 2) ((weightIsometry w 2).symm (deletedL2Conjugation a).val) =
    periodOneL2Conjugation ((weightIsometry w 2) ((weightIsometry w 2).symm a.val))
  rw [LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem meanZeroWeightedProjection_conjugation (w : Weight) (hw : ∀ j, w (-j) = w j)
    (z : WeightedCoeff w 2) :
    meanZeroWeightedProjectionCLM w (conjugateReflection w hw z) =
      deletedL2Conjugation (meanZeroWeightedProjectionCLM w z) := by
  change Coeff.deleteCoordinateTo 0 ((weightIsometry w 2) (conjugateReflection w hw z)) = _
  rw [←weightIsometry_conjugateReflection w hw]
  exact deleteCoordinateTo_conjugation _

theorem meanZeroWeightedLift_real_iff (w : Weight) (hw : ∀ j, w (-j) = w j)
    (a : DeletedCoeff 2 0) :
    (∀ j : ℤ, (meanZeroWeightedLiftCLM w a).val (-j) =
      conj ((meanZeroWeightedLiftCLM w a).val j)) ↔ deletedL2Conjugation a = a := by
  have he := weightIsometry_fixed_iff_raw w hw (meanZeroWeightedLiftCLM w a)
  have hnorm : (weightIsometry w 2) (meanZeroWeightedLiftCLM w a) = a.val :=
    (weightIsometry w 2).apply_symm_apply a.val
  rw [hnorm] at he
  exact he.symm.trans (deletedL2Conjugation_fixed_iff a).symm

end WeightedCoeff
end NLS
