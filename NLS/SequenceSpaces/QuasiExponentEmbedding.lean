import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.Multiplier

/-!
# Contractive sequence inclusion below exponent one

Counting-measure sequence norms decrease when the exponent increases,
even when the source exponent is below one. The existing Banach-space
continuous linear map requires exponent at least one; this estimate
works directly with the underlying `lp` coefficient values.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {r s : ℝ≥0∞}

private theorem norm_quasiExponentInclusion_le_one
    (hr : 0 < r) (hs : 0 < s) (hsTop : s ≠ ⊤)
    (hrs : r ≤ s) (a : Coeff r) (ha : ‖a‖ ≤ 1) :
    ‖(⟨fun n : ℤ => a n, (lp.memℓp a).of_exponent_ge hrs⟩ : Coeff s)‖ ≤ 1 := by
  have hrTop : r ≠ ⊤ := ne_top_of_le_ne_top hsTop hrs
  have hrr : 0 < r.toReal := ENNReal.toReal_pos hr.ne' hrTop
  have hsr : 0 < s.toReal := ENNReal.toReal_pos hs.ne' hsTop
  apply lp.norm_le_of_forall_sum_le hsr zero_le_one
  intro S
  calc
    ∑ n ∈ S, ‖(⟨fun n : ℤ => a n,
        (lp.memℓp a).of_exponent_ge hrs⟩ : Coeff s) n‖ ^ s.toReal
        ≤ ∑ n ∈ S, ‖a n‖ ^ r.toReal := by
          apply Finset.sum_le_sum
          intro n _
          exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _)
            ((lp.norm_apply_le_norm hr.ne' a n).trans ha)
            hrr.le ((ENNReal.toReal_le_toReal hrTop hsTop).mpr hrs)
    _ ≤ ‖a‖ ^ r.toReal := lp.sum_rpow_le_norm_rpow hrr a S
    _ ≤ 1 ^ s.toReal := by
      rw [Real.one_rpow]
      exact Real.rpow_le_one (lp.norm_nonneg' a) ha hrr.le

/-- Increasing a sequence exponent is norm-contracting, including a
source exponent strictly between zero and one. -/
theorem norm_quasiExponentInclusion_le
    (hr : 0 < r) (hs : 0 < s) (hsTop : s ≠ ⊤)
    (hrs : r ≤ s) (a : Coeff r) :
    ‖(⟨fun n : ℤ => a n, (lp.memℓp a).of_exponent_ge hrs⟩ : Coeff s)‖ ≤ ‖a‖ := by
  by_cases ha : a = 0
  · subst a
    have hz : (⟨fun n : ℤ => (0 : Coeff r) n,
        (lp.memℓp (0 : Coeff r)).of_exponent_ge hrs⟩ : Coeff s) = 0 := by
      ext n
      rfl
    rw [hz, lp.norm_zero, lp.norm_zero]
  · have hpos : 0 < ‖a‖ :=
      lt_of_le_of_ne (lp.norm_nonneg' a) (Ne.symm ((lp.norm_eq_zero_iff).not.mpr ha))
    have hb : ‖(‖a‖⁻¹ : ℂ) • a‖ ≤ 1 := by
      rw [lp.norm_const_smul hr.ne']
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, hpos.ne']
    have h := norm_quasiExponentInclusion_le_one hr hs hsTop hrs
      ((‖a‖⁻¹ : ℂ) • a) hb
    have he :
        (⟨fun n : ℤ => ((‖a‖⁻¹ : ℂ) • a) n,
          (lp.memℓp ((‖a‖⁻¹ : ℂ) • a)).of_exponent_ge hrs⟩ : Coeff s) =
          (‖a‖⁻¹ : ℂ) •
            (⟨fun n : ℤ => a n, (lp.memℓp a).of_exponent_ge hrs⟩ : Coeff s) := by
      ext n
      rfl
    rw [he, lp.norm_const_smul hs.ne'] at h
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos] at h
    have hh := mul_le_mul_of_nonneg_left h hpos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul,
      mul_one] using hh

/-- A bounded symbol also multiplies the sequence spaces below
exponent one, with the same norm estimate. -/
theorem norm_multiplier_le_quasi (hr : r ≠ 0)
    (m : Coeff ⊤) (a : Coeff r) :
    ‖multiplier m a‖ ≤ ‖m‖ * ‖a‖ := by
  have h : ‖multiplier m a‖ ≤ ‖(‖m‖ : ℂ) • a‖ := by
    apply lp.norm_mono hr
    intro n
    simp only [multiplier_apply, norm_mul, lp.coeFn_smul, Pi.smul_apply,
      norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (lp.norm_nonneg' m)]
    exact mul_le_mul_of_nonneg_right
      (lp.norm_apply_le_norm (by simp) m n) (norm_nonneg _)
  rw [lp.norm_const_smul hr] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (lp.norm_nonneg' m)] using h

end NLS.Coeff
