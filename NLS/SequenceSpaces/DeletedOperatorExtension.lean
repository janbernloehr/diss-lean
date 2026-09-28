import NLS.SequenceSpaces.DeletedCoordinate
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Extending a deleted-coordinate operator to the full sequence space

Lemma 12.10 compares the selected psi Jacobians for different deleted
indices by extending each one to the same `ℓᵖ` space. The deleted row
and column are set to zero except for a chosen scalar on the diagonal.
This file constructs that block extension for any bounded operator.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Deleting one coordinate is contractive in every `ℓᵖ` norm. -/
theorem norm_deleteCoordinateTo_le_one (n : ℤ) :
    ‖deleteCoordinateTo (p := p) n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro a
  change ‖deleteCoordinate n a‖ ≤ 1 * ‖a‖
  rw [one_mul]
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro m
  by_cases hmn : m = n
  · subst m
    simp
  · rw [deleteCoordinate_apply_other n m hmn]

/-- Extend an operator on deleted `ℓᵖ` by the scalar `c` on the
omitted coordinate, with zero off-block entries. -/
def deletedOperatorExtension (n : ℤ) (c : ℂ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    Coeff p →L[ℂ] Coeff p :=
  ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).comp
      (Q.comp (deleteCoordinateTo n)) +
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p n).comp
      (c • lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n)

theorem deletedOperatorExtension_apply (n : ℤ) (c : ℂ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) (a : Coeff p) :
    deletedOperatorExtension n c Q a =
      (Q (deleteCoordinateTo n a) : Coeff p) + lp.single p n (c*a n) := by
  rfl

/-- The norm of a full-space block extension is bounded by the
retained-block norm plus the omitted scalar norm. -/
theorem norm_deletedOperatorExtension_le (n : ℤ) (c : ℂ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    ‖deletedOperatorExtension n c Q‖ ≤ ‖Q‖ + ‖c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (norm_nonneg Q) (norm_nonneg c))
  intro a
  have hproj : ‖deleteCoordinateTo n a‖ ≤ ‖a‖ := by
    have h := (deleteCoordinateTo (p := p) n).le_of_opNorm_le
      (norm_deleteCoordinateTo_le_one n) a
    simpa only [one_mul] using h
  have hQ : ‖(Q (deleteCoordinateTo n a) : Coeff p)‖ ≤ ‖Q‖ * ‖a‖ := by
    have h := Q.le_opNorm (deleteCoordinateTo n a)
    simpa only [Submodule.coe_norm] using
      h.trans (mul_le_mul_of_nonneg_left hproj (norm_nonneg Q))
  have hsingle : ‖(lp.single p n (c*a n) : Coeff p)‖ ≤
      ‖c‖ * ‖a‖ := by
    rw [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p)),norm_mul]
    exact mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' a n)
      (norm_nonneg c)
  rw [deletedOperatorExtension_apply]
  have hsum := norm_add_le
    (Q (deleteCoordinateTo n a) : Coeff p) (lp.single p n (c*a n))
  simpa only [add_mul] using hsum.trans (add_le_add hQ hsingle)

/-- The omitted row is exactly the added scalar block. -/
@[simp] theorem deletedOperatorExtension_apply_same (n : ℤ) (c : ℂ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) (a : Coeff p) :
    (deletedOperatorExtension n c Q a) n = c*a n := by
  rw [deletedOperatorExtension_apply]
  change (Q (deleteCoordinateTo n a) : Coeff p) n +
    (lp.single p n (c*a n) : Coeff p) n = c*a n
  rw [show (Q (deleteCoordinateTo n a) : Coeff p) n = 0 from
    (Q (deleteCoordinateTo n a)).property]
  simp

/-- Every retained row is the original deleted operator. -/
theorem deletedOperatorExtension_apply_other (n m : ℤ) (hmn : m ≠ n)
    (c : ℂ) (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) (a : Coeff p) :
    (deletedOperatorExtension n c Q a) m =
      (Q (deleteCoordinateTo n a) : Coeff p) m := by
  rw [deletedOperatorExtension_apply]
  change (Q (deleteCoordinateTo n a) : Coeff p) m +
    (lp.single p n (c*a n) : Coeff p) m = _
  rw [lp.single_apply_ne _ _ _ hmn]
  simp

/-- Deleting the output of the block extension recovers the original
operator applied to the deleted input. -/
theorem deleteCoordinateTo_deletedOperatorExtension (n : ℤ) (c : ℂ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) (a : Coeff p) :
    deleteCoordinateTo n (deletedOperatorExtension n c Q a) =
      Q (deleteCoordinateTo n a) := by
  apply Subtype.ext
  ext m
  by_cases hmn : m = n
  · subst m
    change (deleteCoordinate n (deletedOperatorExtension n c Q a)) n =
      (Q (deleteCoordinateTo n a) : Coeff p) n
    rw [deleteCoordinate_apply_same]
    exact (Q (deleteCoordinateTo n a)).property.symm
  · change (deleteCoordinate n (deletedOperatorExtension n c Q a)) m =
      (Q (deleteCoordinateTo n a) : Coeff p) m
    rw [deleteCoordinate_apply_other n m hmn,
      deletedOperatorExtension_apply_other n m hmn]

/-- The extension restricts to the original operator on the deleted
coordinate subspace. -/
theorem deletedOperatorExtension_apply_deleted (n : ℤ) (c : ℂ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (a : DeletedCoeff p n) :
    deletedOperatorExtension n c Q (a : Coeff p) = (Q a : Coeff p) := by
  have hdel : deleteCoordinateTo n (a : Coeff p) = a := by
    apply Subtype.ext
    exact (deleteCoordinate_eq_self_iff n (a : Coeff p)).2 a.property
  rw [deletedOperatorExtension_apply,hdel]
  have hn : (a : Coeff p) n = 0 := a.property
  simp [hn]

/-- The deleted input column has only its scalar diagonal entry. -/
theorem deletedOperatorExtension_single_same (n : ℤ) (c t : ℂ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    deletedOperatorExtension n c Q (lp.single p n t) =
      lp.single p n (c*t) := by
  rw [deletedOperatorExtension_apply,deleteCoordinateTo_single_same]
  simp

/-- On every retained input column the block extension agrees with
the original deleted-coordinate operator. -/
theorem deletedOperatorExtension_single_other (n k : ℤ) (hkn : k ≠ n)
    (c t : ℂ) (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    deletedOperatorExtension n c Q (lp.single p k t) =
      (Q (deletedSingleCLM n k hkn t) : Coeff p) := by
  rw [deletedOperatorExtension_apply,
    deleteCoordinateTo_single_other n k hkn]
  have hn : (lp.single p k t : Coeff p) n = 0 :=
    lp.single_apply_ne _ _ _ (Ne.symm hkn)
  change (Q (deletedSingleCLM n k hkn t) : Coeff p) +
    lp.single p n (c*(lp.single p k t : Coeff p) n) = _
  rw [hn]
  simp

/-- Block extensions compose by composing their retained operators
and multiplying their omitted-coordinate scalars. -/
theorem deletedOperatorExtension_comp (n : ℤ) (c d : ℂ)
    (Q R : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    (deletedOperatorExtension n c Q).comp
        (deletedOperatorExtension n d R) =
      deletedOperatorExtension n (c*d) (Q.comp R) := by
  ext a m
  by_cases hmn : m = n
  · subst m
    simp [mul_assoc]
  · rw [ContinuousLinearMap.comp_apply,
      deletedOperatorExtension_apply_other n m hmn,
      deleteCoordinateTo_deletedOperatorExtension,
      deletedOperatorExtension_apply_other n m hmn]
    rfl

/-- Identity on the retained block and scalar one on the omitted
coordinate give the identity on the full sequence space. -/
@[simp] theorem deletedOperatorExtension_id (n : ℤ) :
    deletedOperatorExtension (p := p) n 1
      (ContinuousLinearMap.id ℂ (DeletedCoeff p n)) =
        ContinuousLinearMap.id ℂ (Coeff p) := by
  ext a m
  by_cases hmn : m = n
  · subst m
    simp
  · rw [deletedOperatorExtension_apply_other n m hmn]
    change (deleteCoordinate n a) m = a m
    exact deleteCoordinate_apply_other n m hmn a

/-- The extension used in Lemma 12.10 has value two at its deleted
diagonal entry. -/
def deletedJacobianExtension (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    Coeff p →L[ℂ] Coeff p :=
  deletedOperatorExtension n 2 Q

/-- An invertible deleted operator has an invertible block extension
whenever the scalar at the omitted coordinate is nonzero. -/
theorem deletedOperatorExtension_bijective_of_bijective
    (n : ℤ) (c : ℂ) (hc : c ≠ 0)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (hQ : Function.Bijective Q) :
    Function.Bijective (deletedOperatorExtension n c Q) := by
  let e := ContinuousLinearEquiv.ofBijective Q
    (LinearMap.ker_eq_bot.mpr hQ.1)
    (LinearMap.range_eq_top.mpr hQ.2)
  let R : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    e.symm.toContinuousLinearMap
  let T := deletedOperatorExtension n c Q
  let S := deletedOperatorExtension n c⁻¹ R
  have hRQ : R.comp Q = ContinuousLinearMap.id ℂ (DeletedCoeff p n) := by
    apply ContinuousLinearMap.ext
    intro a
    change e.symm (e a) = a
    exact e.symm_apply_apply a
  have hQR : Q.comp R = ContinuousLinearMap.id ℂ (DeletedCoeff p n) := by
    apply ContinuousLinearMap.ext
    intro a
    change e (e.symm a) = a
    exact e.apply_symm_apply a
  have hST : S.comp T = ContinuousLinearMap.id ℂ (Coeff p) := by
    change (deletedOperatorExtension n c⁻¹ R).comp
      (deletedOperatorExtension n c Q) = _
    rw [deletedOperatorExtension_comp,hRQ,inv_mul_cancel₀ hc,
      deletedOperatorExtension_id]
  have hTS : T.comp S = ContinuousLinearMap.id ℂ (Coeff p) := by
    change (deletedOperatorExtension n c Q).comp
      (deletedOperatorExtension n c⁻¹ R) = _
    rw [deletedOperatorExtension_comp,hQR,mul_inv_cancel₀ hc,
      deletedOperatorExtension_id]
  have hleft : Function.LeftInverse S T := by
    intro a
    have h := congrArg (fun A : Coeff p →L[ℂ] Coeff p => A a) hST
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hright : Function.RightInverse S T := by
    intro a
    have h := congrArg (fun A : Coeff p →L[ℂ] Coeff p => A a) hTS
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  exact ⟨hleft.injective,hright.surjective⟩

/-- If a block extension is bijective, then its retained operator is
bijective. This direction does not require a nonzero scalar. -/
theorem deletedOperator_bijective_of_extension_bijective
    (n : ℤ) (c : ℂ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (hQ : Function.Bijective (deletedOperatorExtension n c Q)) :
    Function.Bijective Q := by
  constructor
  · intro a b hab
    have hext : deletedOperatorExtension n c Q (a : Coeff p) =
        deletedOperatorExtension n c Q (b : Coeff p) := by
      rw [deletedOperatorExtension_apply_deleted,
        deletedOperatorExtension_apply_deleted,hab]
    exact Subtype.ext (hQ.1 hext)
  · intro b
    obtain ⟨a,ha⟩ := hQ.2 (b : Coeff p)
    refine ⟨deleteCoordinateTo n a,?_⟩
    rw [← deleteCoordinateTo_deletedOperatorExtension n c Q a,ha]
    apply Subtype.ext
    exact (deleteCoordinate_eq_self_iff n (b : Coeff p)).2 b.property

/-- The `2`-extension is bijective exactly when the deleted operator
is bijective. -/
theorem deletedJacobianExtension_bijective_iff (n : ℤ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    Function.Bijective (deletedJacobianExtension n Q) ↔
      Function.Bijective Q := by
  constructor
  · exact deletedOperator_bijective_of_extension_bijective n 2 Q
  · exact deletedOperatorExtension_bijective_of_bijective n 2 (by norm_num) Q

/-- The full-space operator norm controls the deleted-block norm. In
particular, a uniform bound on extended inverses will give one on the
original inverse Jacobians. -/
theorem norm_deletedOperator_le_norm_extension (n : ℤ) (c : ℂ)
    (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) :
    ‖Q‖ ≤ ‖deletedOperatorExtension n c Q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  have hbound := (deletedOperatorExtension n c Q).le_opNorm (a : Coeff p)
  rw [deletedOperatorExtension_apply_deleted] at hbound
  simpa only [Submodule.coe_norm] using hbound

end NLS.Coeff
