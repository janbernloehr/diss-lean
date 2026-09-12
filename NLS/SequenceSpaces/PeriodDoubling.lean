import NLS.SequenceSpaces.Insertion
import NLS.SequenceSpaces.Parity

/-!
# Canonical period-one coefficients inside the period-two space

A period-one frequency `n` becomes period-two frequency `2n`. Inserting zeros
at odd frequencies preserves the coefficient norm, including the endpoints,
and is onto the closed even subspace. Convolution respects this embedding.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical period-one to period-two coefficient embedding. -/
def periodDouble : Coeff p →ₗᵢ[ℂ] Coeff p := insertIsometry (parityEmbedding 0)

@[simp] theorem periodDouble_even (a : Coeff p) (n : ℤ) : periodDouble a (2 * n) = a n := by
  change insert (parityEmbedding 0) a (2 * n) = a n
  simpa using insert_apply_image (parityEmbedding 0) a n

@[simp] theorem periodDouble_odd (a : Coeff p) (n : ℤ) : periodDouble a (2 * n + 1) = 0 :=
  insert_parity_other 0 1 (by norm_num) a n

/-- The inserted sequence has exactly even support. -/
theorem periodDouble_mem (a : Coeff p) : periodDouble a ∈ paritySubspace 0 := by
  rw [mem_paritySubspace]
  intro n hn
  have he : n = 2 * (n / 2) + 1 := by omega
  rw [he, periodDouble_odd]

@[simp] theorem norm_periodDouble (a : Coeff p) : ‖periodDouble a‖ = ‖a‖ := periodDouble.norm_map a

/-- Reading the even frequencies gives a coefficient sequence at the same exponent. -/
def periodHalve (a : Coeff p) : Coeff p := ⟨fun n => a (2 * n), by
  change Memℓp (fun n => a (2 * n)) p
  by_cases hp : p = ⊤
  · subst p
    apply memℓp_infty
    refine ⟨‖a‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact lp.norm_apply_le_norm (by simp) a (2 * n)
  · have hp0 : 0 < p.toReal := ENNReal.toReal_pos
      (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne' hp
    rw [memℓp_gen_iff hp0]
    exact ((lp.memℓp a).summable hp0).comp_injective (show Function.Injective (fun n : ℤ => 2 * n) by
      intro m n h; change 2 * m = 2 * n at h; omega)⟩

@[simp] theorem periodHalve_apply (a : Coeff p) (n : ℤ) : periodHalve a n = a (2 * n) := rfl

@[simp] theorem periodHalve_periodDouble (a : Coeff p) : periodHalve (periodDouble a) = a := by
  ext n
  simp

/-- Reinserting the even samples is precisely the previously constructed even projection. -/
theorem periodDouble_periodHalve (a : Coeff p) : periodDouble (periodHalve a) = parityProjection 0 a := by
  ext n
  by_cases hn : n % 2 = 0
  · have he : n = 2 * (n / 2) := by omega
    simp only [parityProjection_apply, Int.zero_emod, hn, if_true]
    rw [he, periodDouble_even, periodHalve_apply]
  · have he : n = 2 * (n / 2) + 1 := by omega
    simp only [parityProjection_apply, Int.zero_emod, hn, if_false]
    rw [he, periodDouble_odd]

/-- Reading even coefficients is contractive even when the input also has odd modes. -/
theorem norm_periodHalve_le (a : Coeff p) : ‖periodHalve a‖ ≤ ‖a‖ := by
  rw [← norm_periodDouble (periodHalve a), periodDouble_periodHalve]
  exact norm_parityProjection_apply_le 0 a

/-- The coefficient embedding is an isometric equivalence onto the even subspace. -/
def periodDoubleEquiv : Coeff p ≃ₗᵢ[ℂ] paritySubspace (p := p) 0 where
  toFun a := ⟨periodDouble a, periodDouble_mem a⟩
  invFun a := periodHalve a.val
  left_inv := periodHalve_periodDouble
  right_inv a := by
    apply Subtype.ext
    exact (periodDouble_periodHalve a.val).trans ((parityProjection_eq_self_iff 0 a.val).mpr a.property)
  map_add' a b := by apply Subtype.ext; exact periodDouble.map_add a b
  map_smul' c a := by apply Subtype.ext; exact periodDouble.map_smul c a
  norm_map' := norm_periodDouble

@[simp] theorem periodDoubleEquiv_val (a : Coeff p) : (periodDoubleEquiv a).val = periodDouble a := rfl

/-- The inverse reads the even indices, including the negative ones. -/
@[simp] theorem periodDoubleEquiv_symm_apply (a : paritySubspace (p := p) 0) (n : ℤ) :
    periodDoubleEquiv.symm a n = a.val (2 * n) := rfl

/-- A period-one convolution is the same convolution after insertion into even frequencies. -/
theorem periodDouble_convolution (φ : Coeff p) (a : Coeff 1) :
    periodDouble (convolution φ a) = convolution (periodDouble φ) (periodDouble a) := by
  have hmem := convolution_mem_paritySubspace (periodDouble φ) (periodDouble_mem φ)
    0 (periodDouble a) (periodDouble_mem a)
  ext n
  by_cases hn : n % 2 = 0
  · have he : n = 2 * (n / 2) := by omega
    rw [he, periodDouble_even, convolution_apply, convolution_apply]
    have hs := (parityEmbedding 0).injective.tsum_eq
      (f := fun k : ℤ => periodDouble φ (2 * (n / 2) - k) * periodDouble a k) (by
        intro k hk
        by_contra hout
        have hz := insert_apply_outside (parityEmbedding 0) a k hout
        exact hk (by change _ * insert (parityEmbedding 0) a k = 0; rw [hz, mul_zero]))
    rw [← hs]
    apply tsum_congr
    intro k
    simp only [parityEmbedding_apply, add_zero]
    rw [show 2 * (n / 2) - 2 * k = 2 * (n / 2 - k) by ring, periodDouble_even, periodDouble_even]
  · exact ((mem_paritySubspace 0 _).mp (periodDouble_mem (convolution φ a)) n (by simpa using hn)).trans
      (((mem_paritySubspace 0 _).mp hmem n (by simpa using hn)).symm)

end NLS.Coeff
