import NLS.SequenceSpaces.Basic

/-!
# Translation of Fourier coefficients

Reindexing by a bijection preserves the `lp` norm. Translation is the special
case used to construct convolution as an absolutely convergent Banach-space sum.
-/

open scoped ENNReal
noncomputable section

namespace NLS.Coeff

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Permute Fourier coefficients by an equivalence of integer indices. -/
def reindex (e : ℤ ≃ ℤ) (a : Coeff p) : Coeff p :=
  ⟨fun n => a (e n), by
    change Memℓp (fun n => a (e n)) p
    by_cases hp : p = ⊤
    · subst p
      apply memℓp_infty
      refine ⟨‖a‖, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact lp.norm_apply_le_norm (by simp) a (e n)
    · have hp₀ : 0 < p.toReal := ENNReal.toReal_pos
        (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp
      rw [memℓp_gen_iff hp₀]
      exact e.summable_iff.mpr ((lp.memℓp a).summable hp₀)⟩

@[simp]
theorem reindex_apply (e : ℤ ≃ ℤ) (a : Coeff p) (n : ℤ) :
    reindex e a n = a (e n) := rfl

@[simp]
theorem norm_reindex (e : ℤ ≃ ℤ) (a : Coeff p) : ‖reindex e a‖ = ‖a‖ := by
  by_cases hp : p = ⊤
  · subst p
    apply le_antisymm
    · exact lp.norm_le_of_forall_le (norm_nonneg a)
        (fun n => lp.norm_apply_le_norm (by simp) a (e n))
    · apply lp.norm_le_of_forall_le (norm_nonneg (reindex e a))
      intro n
      simpa using lp.norm_apply_le_norm (by simp) (reindex e a) (e.symm n)
  · have hp₀ : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp
    rw [lp.norm_eq_tsum_rpow hp₀, lp.norm_eq_tsum_rpow hp₀]
    congr 1
    exact e.tsum_eq (fun n => ‖a n‖ ^ p.toReal)

/-- Reindexing as a linear isometry equivalence. -/
def reindexIsometry (e : ℤ ≃ ℤ) : Coeff p ≃ₗᵢ[ℂ] Coeff p where
  toFun := reindex e
  invFun := reindex e.symm
  left_inv a := by ext n; simp
  right_inv a := by ext n; simp
  map_add' a b := by ext n; rfl
  map_smul' c a := by ext n; rfl
  norm_map' := norm_reindex e

/-- Shift by `k`: the coefficient at `n` becomes the old coefficient at `n-k`. -/
def shift (k : ℤ) : Coeff p ≃ₗᵢ[ℂ] Coeff p :=
  reindexIsometry (Equiv.addRight (-k))

@[simp]
theorem shift_apply (k : ℤ) (a : Coeff p) (n : ℤ) :
    shift k a n = a (n - k) := rfl

@[simp]
theorem norm_shift (k : ℤ) (a : Coeff p) : ‖shift k a‖ = ‖a‖ :=
  (shift k).norm_map a

end NLS.Coeff
