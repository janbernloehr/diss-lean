import NLS.SequenceSpaces.Translation

/-!
# Inserting coefficients along an injective index map

Extend a coefficient sequence by zero outside the image of an embedding.
This preserves the `ℓp` norm, including the supremum endpoint. Even and odd
index insertions will assemble the normalized interval Fourier coefficients.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Insert a sequence along an integer embedding, filling the other indices with zero. -/
def insert (e : ℤ ↪ ℤ) (a : Coeff p) : Coeff p :=
  ⟨Function.extend e a 0, by
    change Memℓp (Function.extend e a 0) p
    by_cases hp : p = ⊤
    · subst p
      apply memℓp_infty
      refine ⟨‖a‖, ?_⟩
      rintro _ ⟨n, rfl⟩
      dsimp only
      by_cases hn : n ∈ Set.range e
      · obtain ⟨k, rfl⟩ := hn
        rw [e.injective.extend_apply]
        exact lp.norm_apply_le_norm (by simp) a k
      · rw [Function.extend_apply' _ _ n hn]
        simp
    · have hpReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
      rw [memℓp_gen_iff hpReal]
      apply (e.injective.summable_iff (fun n hn => ?_)).mp
      · simpa only [Function.comp_def, e.injective.extend_apply] using (lp.memℓp a).summable hpReal
      · simp [Function.extend_apply' _ _ n hn, hpReal.ne']⟩

@[simp] theorem insert_apply_image (e : ℤ ↪ ℤ) (a : Coeff p) (n : ℤ) :
    insert e a (e n) = a n := e.injective.extend_apply a 0 n

theorem insert_apply_outside (e : ℤ ↪ ℤ) (a : Coeff p) (n : ℤ) (hn : n ∉ Set.range e) :
    insert e a n = 0 := Function.extend_apply' (f := e) a (0 : ℤ → ℂ) n hn

@[simp] theorem norm_insert (e : ℤ ↪ ℤ) (a : Coeff p) : ‖insert e a‖ = ‖a‖ := by
  by_cases hp : p = ⊤
  · subst p
    apply le_antisymm
    · apply lp.norm_le_of_forall_le (norm_nonneg a)
      intro n
      by_cases hn : n ∈ Set.range e
      · obtain ⟨k, rfl⟩ := hn
        rw [insert_apply_image]
        exact lp.norm_apply_le_norm (by simp) a k
      · rw [insert_apply_outside e a n hn]; simp
    · apply lp.norm_le_of_forall_le (norm_nonneg (insert e a))
      intro n
      simpa only [insert_apply_image] using lp.norm_apply_le_norm (by simp) (insert e a) (e n)
  · have hpReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
    rw [lp.norm_eq_tsum_rpow hpReal, lp.norm_eq_tsum_rpow hpReal]
    congr 1
    have he := e.injective.tsum_eq (f := fun n => ‖insert e a n‖ ^ p.toReal) (by
      intro n hn
      by_contra h
      have hz := insert_apply_outside e a n h
      simp [hz, hpReal.ne'] at hn)
    simpa only [insert_apply_image] using he.symm

/-- Zero insertion is a linear isometry. -/
def insertIsometry (e : ℤ ↪ ℤ) : Coeff p →ₗᵢ[ℂ] Coeff p where
  toFun := insert e
  map_add' a b := by
    apply lp.ext
    funext n
    by_cases hn : n ∈ Set.range e
    · obtain ⟨k, rfl⟩ := hn
      simp
    · simp [insert_apply_outside e _ n hn]
  map_smul' c a := by
    apply lp.ext
    funext n
    by_cases hn : n ∈ Set.range e
    · obtain ⟨k, rfl⟩ := hn
      simp
    · simp [insert_apply_outside e _ n hn]
  norm_map' := norm_insert e

/-- The affine even/odd index embeddings, retaining the integer sign convention. -/
def parityEmbedding (r : ℤ) : ℤ ↪ ℤ := ⟨fun n => 2*n+r, by intro m n h; dsimp at h; omega⟩

@[simp] theorem parityEmbedding_apply (r n : ℤ) : parityEmbedding r n = 2*n+r := rfl

theorem insert_parity_other (r s : ℤ) (hrs : r % 2 ≠ s % 2) (a : Coeff p) (n : ℤ) :
    insert (parityEmbedding r) a (2*n+s) = 0 := by
  apply insert_apply_outside
  rintro ⟨k, hk⟩
  change 2*k+r = 2*n+s at hk
  omega

end NLS.Coeff
