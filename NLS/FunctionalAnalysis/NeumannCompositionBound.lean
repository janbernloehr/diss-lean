import NLS.SequenceSpaces.NearbyInverse

/-!
# The composition-norm Neumann perturbation bound

The exact condition norm(Q-inverse composed with delta-Q) at most one half
gives a genuine two-sided inverse with norm at most twice the original bound.
-/

noncomputable section
namespace NLS
theorem inverse_norm_le_two_mul_of_composition_near
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T S R R₀ : E →L[ℂ] E)
    (hTR : T.comp R = ContinuousLinearMap.id ℂ E)
    (hR₀S : R₀.comp S = ContinuousLinearMap.id ℂ E)
    (hnear : ‖R₀.comp (S - T)‖ ≤ (1 / 2 : ℝ)) :
    ‖R‖ ≤ 2 * ‖R₀‖ := by
  apply ContinuousLinearMap.opNorm_le_bound R (by positivity)
  intro y
  have hTy : T (R y) = y := by
    have h := congrArg (fun A : E →L[ℂ] E => A y) hTR
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hR₀S_apply (x : E) : R₀ (S x) = x := by
    have h := congrArg (fun A : E →L[ℂ] E => A x) hR₀S
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hidentity : R y = R₀ y + R₀ ((S - T) (R y)) := by
    calc
      R y = R₀ (S (R y)) := (hR₀S_apply _).symm
      _ = R₀ (T (R y) + (S - T) (R y)) := by simp
      _ = R₀ y + R₀ ((S - T) (R y)) := by rw [map_add, hTy]
  have hbound : ‖R y‖ ≤ ‖R₀‖*‖y‖ + ‖R₀.comp (S-T)‖*‖R y‖ := by
    calc
      ‖R y‖ = ‖R₀ y + R₀ ((S-T) (R y))‖ := congrArg norm hidentity
      _ ≤ ‖R₀ y‖ + ‖R₀ ((S-T) (R y))‖ := norm_add_le _ _
      _ ≤ ‖R₀‖*‖y‖ + ‖R₀.comp (S-T)‖*‖R y‖ :=
        add_le_add (R₀.le_opNorm y) ((R₀.comp (S-T)).le_opNorm (R y))
  have hsmall := mul_le_mul_of_nonneg_right hnear (norm_nonneg (R y))
  nlinarith

theorem exists_inverse_norm_le_two_mul_of_composition_near
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T S R₀ : E →L[ℂ] E)
    (hSR : S.comp R₀ = ContinuousLinearMap.id ℂ E)
    (hRS : R₀.comp S = ContinuousLinearMap.id ℂ E)
    (hnear : ‖R₀.comp (S-T)‖ ≤ (1/2:ℝ)) :
    ∃ R : E →L[ℂ] E,
      T.comp R = ContinuousLinearMap.id ℂ E ∧
      R.comp T = ContinuousLinearMap.id ℂ E ∧ ‖R‖ ≤ 2*‖R₀‖ := by
  have hsmall : ‖R₀.comp (S-T)‖ < 1 :=
    hnear.trans_lt (by norm_num)
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
  exact ⟨R,hTR,hRT,inverse_norm_le_two_mul_of_composition_near T S R R₀ hTR hRS hnear⟩

/-- The literal perturbation criterion uses the norm of Q-inverse composed with the perturbation. -/
theorem exists_inverse_norm_le_two_mul_of_perturbation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Q R₀ δQ : E →L[ℂ] E)
    (hQR : Q.comp R₀ = ContinuousLinearMap.id ℂ E)
    (hRQ : R₀.comp Q = ContinuousLinearMap.id ℂ E)
    (hnear : ‖R₀.comp δQ‖ ≤ (1/2:ℝ)) :
    ∃ R : E →L[ℂ] E,
      (Q+δQ).comp R = ContinuousLinearMap.id ℂ E ∧
      R.comp (Q+δQ) = ContinuousLinearMap.id ℂ E ∧ ‖R‖ ≤ 2*‖R₀‖ := by
  apply exists_inverse_norm_le_two_mul_of_composition_near (Q+δQ) Q R₀ hQR hRQ
  simpa only [sub_add_cancel_left,ContinuousLinearMap.comp_neg,norm_neg] using hnear

end NLS
