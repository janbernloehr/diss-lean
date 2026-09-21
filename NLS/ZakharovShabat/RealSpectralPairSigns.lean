import NLS.ZakharovShabat.PeriodicSpectralProductCutoffs

/-!
# Signs of real paired spectral products
The exceptional zero-mode denominator and all other squared denominators
are positive. The full normalization is negative, so a cutoff is nonpositive
outside all paired intervals and nonnegative inside exactly one interval.
-/

noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- The spectral normalization is the coercion of a strictly positive real number. -/
theorem spectralPairDenominator_eq_ofReal (n : ℤ) :
    spectralPairDenominator n = ((if n = 0 then 1 else (Real.pi*(n : ℝ))^2 : ℝ) : ℂ) := by
  by_cases hn : n = 0 <;> simp [spectralPairDenominator,hn]

/-- Every paired denominator has strictly positive real part, including the zero mode. -/
theorem spectralPairDenominator_re_pos (n : ℤ) : 0 < (spectralPairDenominator n).re := by
  rw [spectralPairDenominator_eq_ofReal,ofReal_re]
  split_ifs with hn
  · norm_num
  · exact sq_pos_of_ne_zero (mul_ne_zero Real.pi_ne_zero (Int.cast_ne_zero.mpr hn))

/-- Real endpoints give a literal real factor with a positive real denominator. -/
theorem spectralPairFactor_eq_ofReal_of_real (ξ η : ℤ → ℂ)
    (hξ : ∀ n, (ξ n).im = 0) (hη : ∀ n, (η n).im = 0) (x : ℝ) (n : ℤ) :
    spectralPairFactor ξ η x n =
      (((ξ n).re-x)*((η n).re-x)/(spectralPairDenominator n).re : ℝ) := by
  have hl : ξ n = ((ξ n).re : ℂ) := by apply Complex.ext <;> simp [hξ]
  have hr : η n = ((η n).re : ℂ) := by apply Complex.ext <;> simp [hη]
  rw [spectralPairFactor_eq_div,hl,hr,spectralPairDenominator_eq_ofReal]
  simp

/-- Real finite paired products retain the negative full normalization. -/
theorem spectralPairPartialProduct_eq_ofReal_of_real (ξ η : ℤ → ℂ)
    (hξ : ∀ n, (ξ n).im = 0) (hη : ∀ n, (η n).im = 0) (x : ℝ) (N : ℕ) :
    spectralPairPartialProduct ξ η x N =
      ((-4*∏ n ∈ Finset.Icc (-(N : ℤ)) N,
        ((ξ n).re-x)*((η n).re-x)/(spectralPairDenominator n).re : ℝ) : ℂ) := by
  simp only [spectralPairPartialProduct,spectralPairFactor_eq_ofReal_of_real ξ η hξ hη,
    ofReal_mul,ofReal_neg,ofReal_ofNat,ofReal_prod]

/-- If every paired real numerator is nonnegative, the full cutoff has nonpositive real part. -/
theorem spectralPairPartialProduct_re_nonpos (ξ η : ℤ → ℂ)
    (hξ : ∀ n, (ξ n).im = 0) (hη : ∀ n, (η n).im = 0) (x : ℝ)
    (h : ∀ n, 0 ≤ ((ξ n).re-x)*((η n).re-x)) (N : ℕ) :
    (spectralPairPartialProduct ξ η x N).re ≤ 0 := by
  rw [spectralPairPartialProduct_eq_ofReal_of_real ξ η hξ hη,ofReal_re]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    (Finset.prod_nonneg (fun n _ => div_nonneg (h n) (spectralPairDenominator_re_pos n).le))

/-- One nonpositive pair and otherwise nonnegative pairs give a nonnegative full cutoff. -/
theorem spectralPairPartialProduct_re_nonneg (ξ η : ℤ → ℂ)
    (hξ : ∀ n, (ξ n).im = 0) (hη : ∀ n, (η n).im = 0) (x : ℝ) (n : ℤ)
    (hn : ((ξ n).re-x)*((η n).re-x) ≤ 0)
    (h : ∀ k, k ≠ n → 0 ≤ ((ξ k).re-x)*((η k).re-x)) (N : ℕ) (hN : n.natAbs ≤ N) :
    0 ≤ (spectralPairPartialProduct ξ η x N).re := by
  have hm : n ∈ Finset.Icc (-(N : ℤ)) N := by simp only [Finset.mem_Icc]; omega
  rw [spectralPairPartialProduct_eq_ofReal_of_real ξ η hξ hη,ofReal_re,← Finset.mul_prod_erase _ _ hm]
  apply mul_nonneg_of_nonpos_of_nonpos (by norm_num)
  exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hn (spectralPairDenominator_re_pos n).le)
    (Finset.prod_nonneg (fun k hk => div_nonneg (h k (Finset.mem_erase.mp hk).1) (spectralPairDenominator_re_pos k).le))

end NLS.ZakharovShabat
