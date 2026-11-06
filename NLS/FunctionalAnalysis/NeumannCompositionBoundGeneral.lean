import NLS.SequenceSpaces.NearbyInverse

/-!
# The composition-norm Neumann perturbation bound

The exact condition norm(Q-inverse composed with delta-Q) at most one half
gives a genuine two-sided inverse with norm at most twice the original bound.
-/

noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
theorem inverse_norm_le_two_mul_of_composition_near
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T S R R₀ : E →L[𝕜] E)
    (hTR : T.comp R = ContinuousLinearMap.id 𝕜 E)
    (hR₀S : R₀.comp S = ContinuousLinearMap.id 𝕜 E)
    (hnear : ‖R₀.comp (S - T)‖ ≤ (1 / 2 : ℝ)) :
    ‖R‖ ≤ 2 * ‖R₀‖ := by
  apply ContinuousLinearMap.opNorm_le_bound R (by positivity)
  intro y
  have hTy : T (R y) = y := by
    have h := congrArg (fun A : E →L[𝕜] E => A y) hTR
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hR₀S_apply (x : E) : R₀ (S x) = x := by
    have h := congrArg (fun A : E →L[𝕜] E => A x) hR₀S
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
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (T S R₀ : E →L[𝕜] E)
    (hSR : S.comp R₀ = ContinuousLinearMap.id 𝕜 E)
    (hRS : R₀.comp S = ContinuousLinearMap.id 𝕜 E)
    (hnear : ‖R₀.comp (S-T)‖ ≤ (1/2:ℝ)) :
    ∃ R : E →L[𝕜] E,
      T.comp R = ContinuousLinearMap.id 𝕜 E ∧
      R.comp T = ContinuousLinearMap.id 𝕜 E ∧ ‖R‖ ≤ 2*‖R₀‖ := by
  have hsmall : ‖R₀.comp (S-T)‖ < 1 :=
    hnear.trans_lt (by norm_num)
  have hunit := isUnit_one_sub_of_norm_lt_one hsmall
  have heq : (1 : E →L[𝕜] E)-R₀.comp (S-T) = R₀.comp T := by
    rw [ContinuousLinearMap.comp_sub,hRS]
    change (1 : E →L[𝕜] E)-(1-R₀.comp T) = _
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
  have hTR : T.comp R = ContinuousLinearMap.id 𝕜 E := by
    ext x
    exact e.apply_symm_apply x
  have hRT : R.comp T = ContinuousLinearMap.id 𝕜 E := by
    ext x
    exact e.symm_apply_apply x
  exact ⟨R,hTR,hRT,inverse_norm_le_two_mul_of_composition_near T S R R₀ hTR hRS hnear⟩


end NLS.FunctionalAnalysis
