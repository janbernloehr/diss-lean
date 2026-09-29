import NLS.SequenceSpaces.UniformInverseBound
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Existence and bounds for inverses of nearby operators

The Neumann criterion proves actual invertibility of a sufficiently
small perturbation. The quantitative inverse estimate then gives a
two-sided bounded inverse with at most twice the original norm.
-/

noncomputable section
namespace NLS

theorem exists_inverse_norm_le_two_mul_of_near
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T S R₀ : E →L[ℂ] E)
    (hSR : S.comp R₀ = ContinuousLinearMap.id ℂ E)
    (hRS : R₀.comp S = ContinuousLinearMap.id ℂ E)
    (hnear : ‖R₀‖ * ‖S-T‖ ≤ (1/2:ℝ)) :
    ∃ R : E →L[ℂ] E,
      T.comp R = ContinuousLinearMap.id ℂ E ∧
      R.comp T = ContinuousLinearMap.id ℂ E ∧ ‖R‖ ≤ 2*‖R₀‖ := by
  have hsmall : ‖R₀.comp (S-T)‖ < 1 :=
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans hnear).trans_lt (by norm_num)
  have hunit := isUnit_one_sub_of_norm_lt_one hsmall
  have heq : (1 : E →L[ℂ] E)-R₀.comp (S-T) = R₀.comp T := by
    rw [ContinuousLinearMap.comp_sub,hRS]
    change (1 : E →L[ℂ] E)-(1-R₀.comp T) = _
    abel
  rw [heq] at hunit
  have hSu : IsUnit S := ⟨⟨S,R₀,hSR,hRS⟩,rfl⟩
  have hTu : IsUnit T := by
    have h := hSu.mul hunit
    have hST : S*(R₀.comp T) = T := by
      change S.comp (R₀.comp T) = T
      rw [← ContinuousLinearMap.comp_assoc,hSR,ContinuousLinearMap.id_comp]
    rwa [hST] at h
  have hbij := ContinuousLinearMap.isUnit_iff_bijective.mp hTu
  let e := ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  let R := e.symm.toContinuousLinearMap
  have hTR : T.comp R = ContinuousLinearMap.id ℂ E := by
    ext x
    exact e.apply_symm_apply x
  have hRT : R.comp T = ContinuousLinearMap.id ℂ E := by
    ext x
    exact e.symm_apply_apply x
  exact ⟨R,hTR,hRT,inverse_norm_le_two_mul_of_near T S R R₀ hTR hRS hnear⟩

end NLS

open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A two-sided inverse of a full deleted-Jacobian extension gives
a two-sided inverse of the original block, with no larger norm. -/
theorem exists_deleted_inverse_of_extension_inverse
    (n : ℤ) (Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (R : Coeff p →L[ℂ] Coeff p)
    (hQR : (deletedJacobianExtension n Q).comp R = ContinuousLinearMap.id ℂ (Coeff p))
    (hRQ : R.comp (deletedJacobianExtension n Q) = ContinuousLinearMap.id ℂ (Coeff p)) :
    ∃ S : DeletedCoeff p n →L[ℂ] DeletedCoeff p n,
      Q.comp S = ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
      S.comp Q = ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧ ‖S‖ ≤ ‖R‖ := by
  have hfull : Function.Bijective (deletedJacobianExtension n Q) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp ⟨⟨_,R,hQR,hRQ⟩,rfl⟩
  have hbij := (deletedJacobianExtension_bijective_iff n Q).mp hfull
  let e := ContinuousLinearEquiv.ofBijective Q
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  let S := e.symm.toContinuousLinearMap
  have hQS : Q.comp S = ContinuousLinearMap.id ℂ (DeletedCoeff p n) := by
    apply ContinuousLinearMap.ext
    intro x
    exact e.apply_symm_apply x
  have hSQ : S.comp Q = ContinuousLinearMap.id ℂ (DeletedCoeff p n) := by
    apply ContinuousLinearMap.ext
    intro x
    exact e.symm_apply_apply x
  have heq : deletedOperatorExtension n (1/2:ℂ) S = R := by
    apply ContinuousLinearMap.ext
    intro x
    apply hfull.1
    have hleft := congrArg (fun A : Coeff p →L[ℂ] Coeff p => A x)
      (deletedJacobianExtension_inverse_comp n Q S hQS)
    have hright := congrArg (fun A : Coeff p →L[ℂ] Coeff p => A x) hQR
    exact hleft.trans hright.symm
  refine ⟨S,hQS,hSQ,?_⟩
  calc
    ‖S‖ ≤ ‖deletedOperatorExtension n (1/2:ℂ) S‖ := norm_deletedOperator_le_norm_extension n _ S
    _ = ‖R‖ := congrArg norm heq

end NLS.Coeff
