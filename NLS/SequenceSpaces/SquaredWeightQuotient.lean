import NLS.SequenceSpaces.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# An lp quotient by squared weights, including zero weights

A squared-weight pointwise bound forces the numerator to vanish at
every zero weight. Division then gives an actual lp quotient with its
norm controlled by the original majorant. This packages the final
sequence-space step of Lemma 12.12 without excluding collapsed gaps.
-/

noncomputable section
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A squared-weight majorant gives an actual lp quotient, with exact
factorization also at zero weights and the same norm bound. -/
theorem exists_coeff_squared_weight_quotient (γ δ : ℤ → ℂ)
    (B : Coeff p) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ m, ‖δ m‖ ≤ C*‖γ m‖^2*‖B m‖) :
    ∃ A : Coeff p, (∀ m, A m = δ m/(γ m)^2) ∧
      (∀ m, δ m = (γ m)^2*A m) ∧ ‖A‖ ≤ C*‖B‖ := by
  let q : ℤ → ℂ := fun m => δ m/(γ m)^2
  have hzero m (hm : γ m = 0) : δ m = 0 := by
    have h := hbound m
    simp only [hm,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero,zero_mul] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hpoint m : ‖q m‖ ≤ C*‖B m‖ := by
    by_cases hm : γ m = 0
    · simp only [q,hm,zero_pow (by norm_num : (2 : ℕ) ≠ 0),div_zero,norm_zero]
      exact mul_nonneg hC (norm_nonneg _)
    · dsimp only [q]
      rw [norm_div,norm_pow]
      apply (div_le_iff₀ (by positivity : 0 < ‖γ m‖^2)).mpr
      nlinarith [hbound m]
  have hmem : Memℓp q p := ((lp.memℓp B).norm.const_mul C).mono (fun m => hpoint m)
  let A : Coeff p := ⟨q,hmem⟩
  refine ⟨A,fun _ => rfl,?_,?_⟩
  · intro m
    change δ m = (γ m)^2*q m
    by_cases hm : γ m = 0
    · simp only [hm,hzero m hm,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul]
    · dsimp only [q]
      field_simp
  · have hD : ‖A‖ ≤ ‖(C : ℂ) • B‖ := by
      apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      intro m
      simp only [lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]
      exact hpoint m
    simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC] using hD

end NLS
