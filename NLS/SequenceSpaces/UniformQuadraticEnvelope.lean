import NLS.SequenceSpaces.ReciprocalNorm

/-! # Source norm bounds from a uniform bound and a quadratic Fourier tail -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- Combining the two bounds gives a summable shifted quadratic envelope. -/
theorem le_shifted_quadratic_of_uniform {a C N r : ℝ} (ha : 0 ≤ a) (hC : 0 < C)
    (hN : 0 < N) (hr : 0 ≤ r) (hmax : a ≤ C) (htail : r^2*a ≤ C*N^2) :
    a/C ≤ 4*N^2/(N+r)^2 := by
  apply (div_le_iff₀ hC).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < N+r))).mpr
  by_cases h : r ≤ N
  · have hs : (N+r)^2 ≤ 4*N^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs ha]
  · have hs : (N+r)^2 ≤ 4*r^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs ha]

/-- A zero-mean sequence with uniform bound C and quadratic tail C N² has norm
at most C times the p-th root of 8N, at every finite Banach exponent. -/
theorem norm_le_of_uniform_quadratic_envelope
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (a : Coeff p) (C N : ℝ) (hC : 0 < C) (hN : 0 < N) (ha0 : a 0 = 0)
    (hmax : ∀ n : ℤ, ‖a n‖ ≤ C)
    (htail : ∀ n : ℤ, |(n : ℝ)|^2 * ‖a n‖ ≤ C*N^2) :
    ‖a‖ ≤ C*(8*N)^(1/p.toReal) := by
  have hp1 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hp0 : 0 < p.toReal := by linarith
  let F := fun n : ℤ => if n = 0 then (0 : ℝ) else (N+|(n : ℝ)|)^(-(2 : ℝ))
  have hs : Summable F := ReciprocalSeries.summable_int_shifted_rpow hN.le (by norm_num)
  have hb (n : ℤ) : ‖a n‖^p.toReal ≤ (C^p.toReal*(4*N^2))*F n := by
    by_cases hn : n = 0
    · subst n
      simp [ha0,hp0.ne',F]
    · have hv0 : 0 ≤ ‖a n‖/C := div_nonneg (norm_nonneg _) hC.le
      have hv1 : ‖a n‖/C ≤ 1 := (div_le_one hC).mpr (hmax n)
      have henv := le_shifted_quadratic_of_uniform (norm_nonneg (a n)) hC hN
        (abs_nonneg (n : ℝ)) (hmax n) (htail n)
      calc
        _ = C^p.toReal*(‖a n‖/C)^p.toReal := by
          rw [← Real.mul_rpow hC.le hv0, mul_div_cancel₀ _ hC.ne']
        _ ≤ C^p.toReal*(‖a n‖/C) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_le_one hv0 hv1 hp1) (by positivity)
        _ ≤ C^p.toReal*(4*N^2/(N+|(n : ℝ)|)^2) :=
          mul_le_mul_of_nonneg_left henv (by positivity)
        _ = _ := by
          dsimp only [F]
          rw [if_neg hn,Real.rpow_neg (by positivity),Real.rpow_two]
          ring
  have hsum : (∑' n : ℤ, ‖a n‖^p.toReal) ≤ C^p.toReal*(8*N) := by
    calc
      _ ≤ ∑' n : ℤ, (C^p.toReal*(4*N^2))*F n :=
        ((lp.memℓp a).summable hp0).tsum_le_tsum hb (hs.mul_left _)
      _ = (C^p.toReal*(4*N^2))*∑' n : ℤ, F n := tsum_mul_left
      _ ≤ (C^p.toReal*(4*N^2))*(2/N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h := ReciprocalSeries.tsum_int_shifted_rpow_le_integral hN (by norm_num : (1 : ℝ) < 2)
        simpa only [show (2 : ℝ)-1 = 1 by norm_num,show (1 : ℝ)-2 = -1 by norm_num,
          div_one,Real.rpow_neg_one,div_eq_mul_inv,inv_one,mul_one,F] using h
      _ = _ := by field_simp; ring
  apply lp.norm_le_of_tsum_le hp0 (by positivity)
  rw [Real.mul_rpow hC.le (by positivity),← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 8*N),
    one_div_mul_cancel hp0.ne',Real.rpow_one]
  exact hsum

end NLS.Coeff
