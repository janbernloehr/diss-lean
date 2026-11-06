import NLS.SequenceSpaces.FunctionOrZero

/-! # Integer-weighted cubic reciprocal rows with Hilbert gap majorants -/
noncomputable section
set_option autoImplicit false
open Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem norm_int_div_sub_le (n k : ℤ) (hkn : k ≠ n) :
    ‖(k : ℂ)/((n-k : ℤ) : ℂ)‖ ≤ ‖(n : ℂ)‖+1 := by
  have hd : (n-k : ℤ) ≠ 0 := sub_ne_zero.mpr hkn.symm
  have hd1 : (1 : ℝ) ≤ |((n-k : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hd
  have hk : |(k : ℝ)| ≤ |(n : ℝ)|+|((n-k : ℤ) : ℝ)| := by
    have he : (n : ℝ)-((n-k : ℤ) : ℝ)=(k : ℝ) := by push_cast; ring
    simpa only [he,Real.norm_eq_abs] using norm_sub_le (n : ℝ) ((n-k : ℤ) : ℝ)
  simp only [norm_div,Complex.norm_intCast]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd1)).mpr
  nlinarith [abs_nonneg (n : ℝ)]

/-- A quadratic majorant constructs the literal ell1 sequence and bounds
its norm. The zero fallback is eliminated coefficient by coefficient. -/
theorem exists_one_of_hilbert_quadratic_majorant (g : Coeff 2) (f : ℤ → ℂ)
    (C : ℝ) (hb : ∀ k, ‖f k‖ ≤ C*‖g k‖^2) :
    ∃ b : Coeff 1, (∀ k, b k=f k) ∧ ‖b‖ ≤ C*‖g‖^2 := by
  have hg : Summable (fun k => ‖g k‖^2) := by
    simpa using (lp.memℓp g).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hs := (hg.mul_left C).of_nonneg_of_le (fun k => norm_nonneg (f k)) hb
  have hm : Memℓp f 1 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one,Real.rpow_one] using hs
  let b : Coeff 1 := ⟨f,hm⟩
  refine ⟨b,fun _ => rfl,?_⟩
  have hnorm : (∑' k : ℤ, ‖g k‖^2)=‖g‖^2 := by
    simpa using (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) g).symm
  have hh := hs.tsum_le_tsum hb (hg.mul_left C)
  rw [tsum_mul_left,hnorm] at hh
  simpa only [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal),
    ENNReal.toReal_one,one_div_one,Real.rpow_one] using hh

/-- The extra signed index factor is absorbed by the reciprocal
off-diagonal denominator. This retains the ACTUAL signed weighted row,
including its diagonal and every zero gap. -/
theorem exists_int_weighted_cubic_row (n : ℤ) (g a : Coeff 2) (f : ℤ → ℂ)
    (R M D : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hg : ‖g‖ ≤ R) (ha : ‖a‖ ≤ M)
    (hdiag : ‖f n‖ ≤ D*‖g n‖^2)
    (hoff : ∀ k, k ≠ n → f k=(g k)^3/((n-k : ℤ) : ℂ)*a k) :
    ∃ b : Coeff 1, (∀ k, b k=(k : ℂ)*f k) ∧
      ‖b‖ ≤ (‖(n : ℂ)‖*D+(‖(n : ℂ)‖+1)*R*M)*R^2 := by
  let C := ‖(n : ℂ)‖*D+(‖(n : ℂ)‖+1)*R*M
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (k : ℤ) : ‖(k : ℂ)*f k‖ ≤ C*‖g k‖^2 := by
    by_cases hkn : k=n
    · subst k
      rw [norm_mul]
      apply (mul_le_mul_of_nonneg_left hdiag (norm_nonneg _)).trans
      have hdC : ‖(n : ℂ)‖*D ≤ C := by
        dsimp only [C]
        exact le_add_of_nonneg_right (by positivity)
      nlinarith [mul_nonneg (sub_nonneg.mpr hdC) (sq_nonneg ‖g n‖)]
    · have he : (k : ℂ)*f k=((k : ℂ)/((n-k : ℤ) : ℂ))*(g k)^3*a k := by
        rw [hoff k hkn]
        ring
      rw [he,norm_mul,norm_mul,norm_pow]
      have hgk : ‖g k‖ ≤ R := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) g k).trans hg
      have hak : ‖a k‖ ≤ M := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) a k).trans ha
      calc
        _ ≤ (‖(n : ℂ)‖+1)*(‖g k‖^2*R)*M := by
          gcongr
          · exact norm_int_div_sub_le n k hkn
          · nlinarith [mul_nonneg (sq_nonneg ‖g k‖) (sub_nonneg.mpr hgk)]
        _ ≤ C*‖g k‖^2 := by
          dsimp [C]
          nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (n : ℂ)) hD) (sq_nonneg ‖g k‖)]
  obtain ⟨b,hbval,hbnorm⟩ := exists_one_of_hilbert_quadratic_majorant g _ C hb
  exact ⟨b,hbval,hbnorm.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg g) hg 2) hC)⟩

end NLS.Coeff
