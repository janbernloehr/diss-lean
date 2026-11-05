import NLS.SequenceSpaces.WeightedSourceSignedCompletion
import NLS.SequenceSpaces.MeanZeroWeightedCoordinates
import NLS.SequenceSpaces.DeletedRealConjugation

/-! # Real weighted source maps commute with physical conjugation

Real-form uniqueness transports reality of a holomorphic map through
independent symmetric source and target weights, including the mean-zero
Hilbert coordinates used by local inverses.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.WeightedCoeff

theorem weightedSource_meanZero_conjugation (v w : Weight)
    (hv : ∀ j, v (-j)=v j) (hw : ∀ j, w (-j)=w j) (η : ℝ) (hη : 0<η)
    (Z : WeightedCoeff v 2 → WeightedCoeff w 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : WeightedCoeff v 2) η))
    (hreal : ∀ q∈ball (0 : WeightedCoeff v 2) η,
      (∀ j : ℤ, q.val (-j)=(starRingEnd ℂ) (q.val j)) →
        ∀ j : ℤ, (Z q).val (-j)=(starRingEnd ℂ) ((Z q).val j)) :
    ∀ a∈ball (0 : DeletedCoeff 2 0) η,
      meanZeroWeightedMap w (fun u => Z ((weightIsometry v 2).symm u)) (deletedL2Conjugation a)=
        deletedL2Conjugation (meanZeroWeightedMap w (fun u => Z ((weightIsometry v 2).symm u)) a) := by
  let I := weightIsometry v 2
  let L := (weightIsometry w 2).toContinuousLinearEquiv.toContinuousLinearMap
  let T : Coeff 2 → Coeff 2 := fun u => L (Z (I.symm u))
  have hmem (u : Coeff 2) (hu : u∈ball 0 η) : I.symm u∈ball (0 : WeightedCoeff v 2) η := by
    simpa only [mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hu
  have hTa : AnalyticOnNhd ℂ T (ball (0 : Coeff 2) η) := fun u hu =>
    (L.analyticAt _).comp ((hZa _ (hmem u hu)).comp (f := I.symm)
      (I.symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt u))
  have he := periodOneL2_real_form_identity isOpen_ball (convex_ball (0 : Coeff 2) η).isPreconnected
    (mem_ball_self hη) T (fun u => periodOneL2Conjugation (T (periodOneL2Conjugation u)))
    hTa (analyticOnNhd_periodOneL2_conjugate T η hTa) (by
      intro u hu hJu
      rw [hJu]
      have hqreal : ∀ j : ℤ, (I.symm u).val (-j)=(starRingEnd ℂ) ((I.symm u).val j) := by
        apply (weightIsometry_fixed_iff_raw v hv (I.symm u)).mp
        simpa only [I,LinearIsometryEquiv.apply_symm_apply] using hJu
      have hout := (weightIsometry_fixed_iff_raw w hw (Z (I.symm u))).mpr (hreal _ (hmem u hu) hqreal)
      exact hout.symm)
  have hconj (u : Coeff 2) (hu : u∈ball 0 η) :
      T (periodOneL2Conjugation u)=periodOneL2Conjugation (T u) := by
    have hh := congrArg periodOneL2Conjugation (he hu)
    simpa only [periodOneL2Conjugation_involutive] using hh.symm
  intro a ha
  have hmem : a.val∈ball (0 : Coeff 2) η := by
    simpa only [mem_ball_zero_iff,Submodule.norm_coe] using ha
  change Coeff.deleteCoordinateTo 0 (T (periodOneL2Conjugation a.val))=_
  rw [hconj a.val hmem]
  exact deleteCoordinateTo_conjugation _

end NLS.WeightedCoeff
