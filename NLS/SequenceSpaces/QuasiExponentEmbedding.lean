import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.SandwichMajorant

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

/-- Taking coefficient magnitudes preserves the quasi-norm at every
positive exponent. -/
theorem norm_magnitude_quasi (hr : r ≠ 0) (a : Coeff r) :
    ‖magnitude a‖ = ‖a‖ := by
  apply le_antisymm
  · apply lp.norm_mono hr
    intro n
    simp
  · apply lp.norm_mono hr
    intro n
    simp

/-- The subadditivity of the `r`th power of the sequence quasi-norm
when `0 < r ≤ 1`. -/
theorem norm_add_rpow_le (hr : 0 < r.toReal) (hr1 : r.toReal ≤ 1)
    (a b : Coeff r) :
    ‖a+b‖ ^ r.toReal ≤ ‖a‖ ^ r.toReal + ‖b‖ ^ r.toReal := by
  rw [lp.norm_rpow_eq_tsum hr, lp.norm_rpow_eq_tsum hr,
    lp.norm_rpow_eq_tsum hr]
  have hpoint (n : ℤ) :
      ‖(a+b) n‖ ^ r.toReal ≤
        ‖a n‖ ^ r.toReal + ‖b n‖ ^ r.toReal := by
    calc
      ‖(a+b) n‖ ^ r.toReal ≤ (‖a n‖+‖b n‖) ^ r.toReal := by
        rw [lp.coeFn_add, Pi.add_apply]
        exact Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hr.le
      _ ≤ _ := Real.rpow_add_le_add_rpow
        (norm_nonneg _) (norm_nonneg _) hr.le hr1
  calc
    (∑' n : ℤ, ‖(a+b) n‖ ^ r.toReal) ≤
        ∑' n : ℤ, (‖a n‖ ^ r.toReal + ‖b n‖ ^ r.toReal) :=
      Summable.tsum_le_tsum hpoint
        ((lp.memℓp (a+b)).summable hr)
        (((lp.memℓp a).summable hr).add ((lp.memℓp b).summable hr))
    _ = _ := (((lp.memℓp a).summable hr).tsum_add
      ((lp.memℓp b).summable hr))

/-- A quantitative triangle bound for sequence quasi-norms with
exponent at most one. -/
theorem norm_add_le_quasi (hr : 0 < r.toReal) (hr1 : r.toReal ≤ 1)
    (a b : Coeff r) :
    ‖a+b‖ ≤
      (‖a‖ ^ r.toReal + ‖b‖ ^ r.toReal) ^ (r.toReal)⁻¹ := by
  have hsum : 0 ≤ ‖a‖ ^ r.toReal + ‖b‖ ^ r.toReal :=
    add_nonneg (Real.rpow_nonneg (lp.norm_nonneg' a) _)
      (Real.rpow_nonneg (lp.norm_nonneg' b) _)
  have htarget : 0 ≤
      (‖a‖ ^ r.toReal + ‖b‖ ^ r.toReal) ^ (r.toReal)⁻¹ :=
    Real.rpow_nonneg hsum _
  apply (Real.rpow_le_rpow_iff (lp.norm_nonneg' (a+b)) htarget hr).mp
  simpa only [Real.rpow_inv_rpow hsum hr.ne'] using
    norm_add_rpow_le hr hr1 a b

/-- A common bound for addition in every positive finite sequence
exponent. The second term handles quasi-norms below exponent one. -/
theorem norm_add_le_uniform (hr : 0 < r.toReal)
    (a b : Coeff r) {A B : ℝ}
    (hA : ‖a‖ ≤ A) (hB : ‖b‖ ≤ B) :
    ‖a+b‖ ≤ max (A+B)
      ((A ^ r.toReal + B ^ r.toReal) ^ (r.toReal)⁻¹) := by
  have hA0 : 0 ≤ A := (lp.norm_nonneg' a).trans hA
  have hB0 : 0 ≤ B := (lp.norm_nonneg' b).trans hB
  by_cases hr1 : r.toReal ≤ 1
  · have hsum : ‖a‖ ^ r.toReal + ‖b‖ ^ r.toReal ≤
        A ^ r.toReal + B ^ r.toReal :=
      add_le_add
        (Real.rpow_le_rpow (lp.norm_nonneg' a) hA hr.le)
        (Real.rpow_le_rpow (lp.norm_nonneg' b) hB hr.le)
    have hsum0 : 0 ≤ ‖a‖ ^ r.toReal + ‖b‖ ^ r.toReal :=
      add_nonneg (Real.rpow_nonneg (lp.norm_nonneg' a) _)
        (Real.rpow_nonneg (lp.norm_nonneg' b) _)
    calc
      ‖a+b‖ ≤
          (‖a‖ ^ r.toReal + ‖b‖ ^ r.toReal) ^ (r.toReal)⁻¹ :=
        norm_add_le_quasi hr hr1 a b
      _ ≤ (A ^ r.toReal + B ^ r.toReal) ^ (r.toReal)⁻¹ :=
        Real.rpow_le_rpow hsum0 hsum (inv_pos.mpr hr).le
      _ ≤ _ := le_max_right _ _
  · have hrTop : r ≠ ⊤ := by
      intro he
      subst r
      norm_num at hr
    have hrOne : 1 ≤ r :=
      (ENNReal.toReal_le_toReal (by norm_num) hrTop).mp
        (by simpa using (le_of_lt (lt_of_not_ge hr1) : 1 ≤ r.toReal))
    haveI : Fact (1 ≤ r) := ⟨hrOne⟩
    exact (norm_add_le a b).trans
      ((add_le_add hA hB).trans (le_max_left _ _))

end NLS.Coeff
