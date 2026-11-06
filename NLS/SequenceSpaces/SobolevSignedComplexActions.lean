import NLS.SequenceSpaces.SobolevSignedActionSequence
import NLS.SequenceSpaces.PositiveDeletedProjectionBounds
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # The complete original action map and its actual native Banach derivative

The bounded bilinear raw signed product has exactly the original action
weight. Its quadratic diagonal extends the real action map holomorphically;
its actual Frechet differential retains every original signed coefficient.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS

/-- Positive signed products as a bounded bilinear map in the original native norms. -/
def sobolevSignedActionProduct (r s : ℝ) (_hrs : r=2*s) :
    WeightedCoeff (Weight.sobolev s) 2 →L[ℂ]
      WeightedCoeff (Weight.sobolev s) 2 →L[ℂ] WeightedCoeff (Weight.sobolev r) 1 :=
  let L := (WeightedCoeff.weightIsometry (Weight.sobolev s) 2).toContinuousLinearEquiv.toContinuousLinearMap
  let R := Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp L
  let P := ((WeightedCoeff.weightIsometry (Weight.sobolev r) 1).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (Coeff.positiveDeletedProjection 1 0)
  ((ContinuousLinearMap.compL ℂ (WeightedCoeff (Weight.sobolev s) 2) (Coeff 1)
    (WeightedCoeff (Weight.sobolev r) 1)) P).comp
      ((Coeff.doublingProduct (p := 1) (q := 2)).bilinearComp L R)

/-- Every raw coefficient has its exact physical signed-product value. -/
theorem sobolevSignedActionProduct_apply (r s : ℝ) (hrs : r=2*s)
    (z h : WeightedCoeff (Weight.sobolev s) 2) (n : ℤ) :
    (sobolevSignedActionProduct r s hrs z h).val n = if 0<n then z.val n*h.val (-n) else 0 := by
  change (Coeff.positiveDeletedProjection 1 0
    (Coeff.doublingProduct (p := 1) (WeightedCoeff.weightIsometry (Weight.sobolev s) 2 z)
      (Coeff.reflection (WeightedCoeff.weightIsometry (Weight.sobolev s) 2 h))) n)/
        (Weight.sobolev r n : ℂ) = _
  rw [Coeff.positiveDeletedProjection_apply]
  by_cases hn : 0<n
  · rw [if_pos (by omega),if_pos hn,Coeff.doublingProduct_apply,Coeff.reflection_apply]
    change ((Weight.sobolev s n : ℂ)*z.val n*((Weight.sobolev s (-n) : ℂ)*h.val (-n)))/
      (Weight.sobolev r n : ℂ)=_
    have hw : (Weight.sobolev r n : ℂ) = (Weight.sobolev s n : ℂ)*(Weight.sobolev s (-n) : ℂ) := by
      rw [hrs,sobolev_action_weight,Complex.ofReal_mul]
    rw [hw]
    apply (div_eq_iff (mul_ne_zero ((Weight.sobolev s).complex_ne_zero n)
      ((Weight.sobolev s).complex_ne_zero (-n)))).mpr
    ring
  · rw [if_neg (by omega),if_neg hn,zero_div]

/-- The literal original action product has Holder constant one. -/
theorem norm_sobolevSignedActionProduct_le (r s : ℝ) (hrs : r=2*s)
    (z h : WeightedCoeff (Weight.sobolev s) 2) :
    ‖sobolevSignedActionProduct r s hrs z h‖ ≤ ‖z‖*‖h‖ := by
  change ‖(WeightedCoeff.weightIsometry (Weight.sobolev r) 1).symm
    (Coeff.positiveDeletedProjection 1 0 (Coeff.doublingProduct (p := 1)
      (WeightedCoeff.weightIsometry (Weight.sobolev s) 2 z)
      (Coeff.reflection (WeightedCoeff.weightIsometry (Weight.sobolev s) 2 h))))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (Coeff.norm_positiveDeletedProjection_le 0 _).trans
    ((Coeff.norm_doublingProduct_le _ _).trans_eq (by simp only [LinearIsometryEquiv.norm_map]))

/-- The complex extension of the full original raw positive action sequence. -/
def sobolevComplexSignedActions (r s : ℝ) (hrs : r=2*s)
    (z : WeightedCoeff (Weight.sobolev s) 2) : WeightedCoeff (Weight.sobolev r) 1 :=
  sobolevSignedActionProduct r s hrs z z

@[simp] theorem sobolevComplexSignedActions_apply (r s : ℝ) (hrs : r=2*s)
    (z : WeightedCoeff (Weight.sobolev s) 2) (n : ℤ) :
    (sobolevComplexSignedActions r s hrs z).val n = if 0<n then z.val n*z.val (-n) else 0 :=
  sobolevSignedActionProduct_apply r s hrs z z n

/-- The actual entire quadratic map in the original raw source and action norms. -/
theorem analyticOnNhd_sobolevComplexSignedActions (r s : ℝ) (hrs : r=2*s) :
    AnalyticOnNhd ℂ (sobolevComplexSignedActions r s hrs) univ := by
  intro z _
  exact ((sobolevSignedActionProduct r s hrs).analyticAt_bilinear (z,z)).comp
    (f := fun h => (h,h)) (analyticAt_id.prod analyticAt_id)

/-- This extension agrees with the literal real signed action sequence. -/
theorem sobolevComplexSignedActions_eq_real (r s : ℝ) (hrs : r=2*s)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    sobolevComplexSignedActions r s hrs z.val = sobolevSignedActionSequence r s hrs z := by
  apply Subtype.ext
  funext n
  rw [sobolevComplexSignedActions_apply,sobolevSignedActionSequence_apply]

/-- The full original real action sequence is real analytic in its native
source and weighted summable target norms. -/
theorem analyticOnNhd_sobolevSignedActionSequence (r s : ℝ) (hrs : r=2*s) :
    AnalyticOnNhd ℝ (sobolevSignedActionSequence r s hrs) univ := by
  intro z _
  let J := (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)).subtypeL
  have hd := ((analyticOnNhd_sobolevComplexSignedActions r s hrs z.val (mem_univ _)).restrictScalars (𝕜 := ℝ)).comp
    (f := J) (J.analyticAt z)
  have he : (sobolevComplexSignedActions r s hrs ∘
      (Subtype.val : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) → WeightedCoeff (Weight.sobolev s) 2)) =
        sobolevSignedActionSequence r s hrs := funext (sobolevComplexSignedActions_eq_real r s hrs)
  have hd' : AnalyticAt ℝ (sobolevComplexSignedActions r s hrs ∘
      (Subtype.val : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) → WeightedCoeff (Weight.sobolev s) 2)) z := by
    simpa only [Function.comp_def] using! hd
  rwa [he] at hd'

/-- The actual bounded complex action differential, in the original norms. -/
def sobolevSignedActionJacobian (r s : ℝ) (hrs : r=2*s)
    (z : WeightedCoeff (Weight.sobolev s) 2) :
    WeightedCoeff (Weight.sobolev s) 2 →L[ℂ] WeightedCoeff (Weight.sobolev r) 1 :=
  sobolevSignedActionProduct r s hrs z+(sobolevSignedActionProduct r s hrs).flip z

theorem sobolevSignedActionJacobian_apply (r s : ℝ) (hrs : r=2*s)
    (z h : WeightedCoeff (Weight.sobolev s) 2) (n : ℤ) :
    (sobolevSignedActionJacobian r s hrs z h).val n =
      if 0<n then z.val n*h.val (-n)+h.val n*z.val (-n) else 0 := by
  change (sobolevSignedActionProduct r s hrs z h).val n+
    (sobolevSignedActionProduct r s hrs h z).val n = _
  rw [sobolevSignedActionProduct_apply,sobolevSignedActionProduct_apply]
  split_ifs <;> simp only [add_zero]

/-- The full action derivative is a Banach-space Frechet derivative, with
no coordinatewise convergence or unproved remainder assumption. -/
theorem hasFDerivAt_sobolevComplexSignedActions (r s : ℝ) (hrs : r=2*s)
    (z : WeightedCoeff (Weight.sobolev s) 2) :
    HasFDerivAt (sobolevComplexSignedActions r s hrs) (sobolevSignedActionJacobian r s hrs z) z := by
  have h := (sobolevSignedActionProduct r s hrs).hasFDerivAt_of_bilinear
    (hasFDerivAt_id z) (hasFDerivAt_id z)
  have he : (sobolevSignedActionProduct r s hrs).precompR _ z (ContinuousLinearMap.id ℂ _)+
      (sobolevSignedActionProduct r s hrs).precompL _ (ContinuousLinearMap.id ℂ _) z =
        sobolevSignedActionJacobian r s hrs z := by
    ext v
    rfl
  rw [show id z = z from rfl,he] at h
  exact h

/-- Literal restriction of the same differential to the physical real mean-zero source. -/
def sobolevRealSignedActionJacobian (r s : ℝ) (hrs : r=2*s)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) →L[ℝ]
      WeightedCoeff (Weight.sobolev r) 1 :=
  ((sobolevSignedActionJacobian r s hrs z.val).restrictScalars ℝ).comp
    (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)).subtypeL

theorem hasFDerivAt_sobolevSignedActionSequence (r s : ℝ) (hrs : r=2*s)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    HasFDerivAt (sobolevSignedActionSequence r s hrs) (sobolevRealSignedActionJacobian r s hrs z) z := by
  let J := (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)).subtypeL
  have hd := ((hasFDerivAt_sobolevComplexSignedActions r s hrs z.val).restrictScalars ℝ).comp z J.hasFDerivAt
  have he : (sobolevComplexSignedActions r s hrs ∘
      (Subtype.val : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) → WeightedCoeff (Weight.sobolev s) 2)) =
        sobolevSignedActionSequence r s hrs :=
    funext (sobolevComplexSignedActions_eq_real r s hrs)
  rw [he] at hd
  simpa only [sobolevRealSignedActionJacobian,J] using! hd

theorem sobolevRealSignedActionJacobian_apply (r s : ℝ) (hrs : r=2*s)
    (z h : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) (n : ℤ) :
    (sobolevRealSignedActionJacobian r s hrs z h).val n =
      if 0<n then z.val.val n*h.val.val (-n)+h.val.val n*z.val.val (-n) else 0 :=
  sobolevSignedActionJacobian_apply r s hrs z.val h.val n

end NLS
