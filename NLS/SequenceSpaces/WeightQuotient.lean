import NLS.SequenceSpaces.SquaredWeightQuotient

/-! # An lp quotient by weights, including zero weights -/
noncomputable section
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A weighted pointwise majorant gives exact factorization even where the weight vanishes. -/
theorem exists_coeff_weight_quotient (γ δ : ℤ → ℂ)
    (B : Coeff p) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ m, ‖δ m‖ ≤ C*‖γ m‖*‖B m‖) :
    ∃ A : Coeff p, (∀ m, A m = δ m/γ m) ∧
      (∀ m, δ m = γ m*A m) ∧ ‖A‖ ≤ C*‖B‖ := by
  let q : ℤ → ℂ := fun m => δ m/γ m
  have hzero m (hm : γ m = 0) : δ m = 0 := by
    have h := hbound m
    simp only [hm,norm_zero,mul_zero,zero_mul] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hpoint m : ‖q m‖ ≤ C*‖B m‖ := by
    by_cases hm : γ m = 0
    · simp only [q,hm,div_zero,norm_zero]
      exact mul_nonneg hC (norm_nonneg _)
    · dsimp only [q]
      rw [norm_div]
      apply (div_le_iff₀ (norm_pos_iff.mpr hm)).mpr
      nlinarith [hbound m]
  have hmem : Memℓp q p := ((lp.memℓp B).norm.const_mul C).mono (fun m => hpoint m)
  let A : Coeff p := ⟨q,hmem⟩
  refine ⟨A,fun _ => rfl,?_,?_⟩
  · intro m
    change δ m = γ m*q m
    by_cases hm : γ m = 0
    · simp only [hm,hzero m hm,zero_mul]
    · dsimp only [q]
      field_simp
  · have hD : ‖A‖ ≤ ‖(C:ℂ) • B‖ := by
      apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      intro m
      simp only [lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]
      exact hpoint m
    simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC] using hD
end NLS
