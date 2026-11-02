import NLS.SequenceSpaces.ConjugateDuality

/-! # Bounded Hilbert operators from an outer-product matrix majorant

An arbitrary matrix dominated by |u_m|*|v_n|, for u,v in l2, defines an
actual bounded operator. Rows and outputs have proved l2 membership;
no formal infinite matrix action is used.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

theorem exists_operator_of_outer_product_dominated_matrix
    (A : ℤ → ℤ → ℂ) (u v : Coeff 2)
    (hA : ∀ m n, ‖A m n‖ ≤ ‖u m‖*‖v n‖) :
    ∃ T : Coeff 2 →L[ℂ] Coeff 2, ‖T‖ ≤ ‖u‖*‖v‖ ∧
      ∀ m n : ℤ, (T (lp.single 2 n 1)) m = A m n := by
  have hr (m : ℤ) : Memℓp (A m) 2 := by
    apply ((lp.memℓp v).const_mul (u m)).mono'
    intro n
    simpa only [norm_mul] using hA m n
  let row (m : ℤ) : Coeff 2 := ⟨A m,hr m⟩
  have hrow (m : ℤ) : ‖row m‖ ≤ ‖u m‖*‖v‖ := by
    calc
      _ ≤ ‖u m • v‖ := lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun n => by
        simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul] using hA m n)
      _ = _ := norm_smul _ _
  have hout (x : Coeff 2) (m : ℤ) :
      ‖dualPairing (row m) x‖ ≤ ‖u m‖*(‖v‖*‖x‖) := by
    calc
      _ ≤ ‖row m‖*‖x‖ := norm_dualPairing_le _ _
      _ ≤ (‖u m‖*‖v‖)*‖x‖ := mul_le_mul_of_nonneg_right (hrow m) (norm_nonneg _)
      _ = _ := by ring
  have hmem (x : Coeff 2) : Memℓp (fun m => dualPairing (row m) x) 2 := by
    apply ((lp.memℓp u).const_mul ((‖v‖*‖x‖ : ℝ) : ℂ)).mono'
    intro m
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg x)),abs_norm,mul_comm] using hout x m
  let L : Coeff 2 →ₗ[ℂ] Coeff 2 := {
    toFun := fun x => ⟨fun m => dualPairing (row m) x,hmem x⟩
    map_add' := by intro x y; ext m; exact map_add (dualPairing (row m)) x y
    map_smul' := by intro c x; ext m; exact map_smul (dualPairing (row m)) c x }
  have hbound (x : Coeff 2) : ‖L x‖ ≤ (‖u‖*‖v‖)*‖x‖ := by
    calc
      _ ≤ ‖((‖v‖*‖x‖ : ℝ) : ℂ) • u‖ :=
        lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun m => by
          simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg x)),mul_comm] using! hout x m)
      _ = _ := by
        rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg x))]
        ring
  let T : Coeff 2 →L[ℂ] Coeff 2 := L.mkContinuous (‖u‖*‖v‖) hbound
  refine ⟨T,ContinuousLinearMap.opNorm_le_bound _ (by positivity) hbound,?_⟩
  intro m n
  change dualPairing (row m) (lp.single 2 n 1) = A m n
  simp only [dualPairing_apply,lp.single_apply,Pi.single_apply,mul_ite,mul_one,mul_zero,tsum_ite_eq]
  rfl

end NLS.Coeff
