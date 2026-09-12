import NLS.SequenceSpaces.SobolevEmbedding
import NLS.SequenceSpaces.ReciprocalSeries
import NLS.SequenceSpaces.Translation

/-!
# The punctured reciprocal lattice in conjugate sequence spaces

The reciprocal integer sequence, with its central entry removed, lies in every
`ℓᑫ` for `q>1`, including infinity. Its Hilbert norm is at most two. This gives
a weight-independent constant for the complementary inverse in Section 6.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- The punctured reciprocal lattice has finite norm for every exponent above one. -/
theorem memlp_puncturedLattice {q : ℝ≥0∞} (hq : 1 < q) :
    Memℓp (fun k : ℤ => if k = 0 then (0 : ℂ) else (k : ℂ)⁻¹) q := by
  by_cases ht : q = ⊤
  · subst q
    apply memℓp_infty
    refine ⟨1, ?_⟩
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = 0
    · simp [hk]
    · simp only [if_neg hk, norm_inv, Complex.norm_intCast]
      apply inv_le_one_of_one_le₀
      exact_mod_cast Int.one_le_abs hk
  · have hqr : 1 < q.toReal := by
      simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top ht).mpr hq
    rw [memℓp_gen_iff (zero_lt_one.trans hqr)]
    apply (ReciprocalSeries.summable_int_shifted_rpow (α := 0) le_rfl hqr).congr
    intro k
    by_cases hk : k = 0
    · simp [hk, (zero_lt_one.trans hqr).ne']
    · simp only [if_neg hk, zero_add, norm_inv, Complex.norm_intCast,
        Real.inv_rpow (abs_nonneg _), Real.rpow_neg (abs_nonneg _)]

/-- Reciprocal integer coefficients, with the origin explicitly removed. -/
def puncturedLattice (q : ℝ≥0∞) (hq : 1 < q) : Coeff q :=
  ⟨fun k => if k = 0 then 0 else (k : ℂ)⁻¹, memlp_puncturedLattice hq⟩

@[simp] theorem puncturedLattice_apply (q : ℝ≥0∞) (hq : 1 < q) (k : ℤ) :
    puncturedLattice q hq k = if k = 0 then 0 else (k : ℂ)⁻¹ := rfl

/-- The source's usable Hilbert constant follows from the bilateral integral bound. -/
theorem norm_puncturedLattice_two_le : ‖puncturedLattice 2 (by norm_num)‖ ≤ 2 := by
  apply lp.norm_le_of_tsum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (by norm_num)
  have he (k : ℤ) : ‖puncturedLattice 2 (by norm_num) k‖ ^ (2 : ℝ≥0∞).toReal =
      if k = 0 then 0 else (0 + |(k : ℝ)|) ^ (-(2 : ℝ)) := by
    by_cases hk : k = 0
    · simp [hk]
    · simp only [puncturedLattice_apply, if_neg hk, norm_inv, Complex.norm_intCast,
        ENNReal.toReal_ofNat, zero_add, Real.inv_rpow (abs_nonneg _), Real.rpow_neg (abs_nonneg _)]
  simp only [he]
  have h := ReciprocalSeries.tsum_int_shifted_rpow_le (α := 0) (q := 2) le_rfl (by norm_num)
  norm_num at h ⊢
  exact h

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A finite constant depending only on `p`, chosen to equal two at `p=2`. -/
def complementaryConstant (hp : p ≠ ⊤) : ℝ :=
  max ‖puncturedLattice p.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖ 2

theorem complementaryConstant_nonneg (hp : p ≠ ⊤) : 0 ≤ complementaryConstant p hp :=
  (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_right _ _)

theorem norm_puncturedLattice_le_complementaryConstant (hp : p ≠ ⊤) :
    ‖puncturedLattice p.conjExponent
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖ ≤ complementaryConstant p hp :=
  le_max_left _ _

@[simp] theorem complementaryConstant_two : complementaryConstant 2 (by norm_num) = 2 := by
  unfold complementaryConstant
  have hq : (2 : ℝ≥0∞).conjExponent = 2 := ENNReal.HolderConjugate.unique 2 _ 2
  have h : ∀ (q : ℝ≥0∞) (h : 1 < q), q = 2 → ‖puncturedLattice q h‖ ≤ 2 := by
    rintro q h rfl
    exact norm_puncturedLattice_two_le
  exact max_eq_right (h _ _ hq)

end NLS.Coeff
