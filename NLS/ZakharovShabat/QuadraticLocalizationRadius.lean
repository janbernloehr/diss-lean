import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The explicit radius in Lemma 25.4 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- The source radius, in terms of a potential norm and a signed frequency. -/
def quadraticLocalizationRadius (P : ℝ) (n : ℤ) : ℝ :=
  P^2/(1+|(n:ℝ)|)+Real.sqrt 2*P/(1+|((2*n:ℤ):ℝ)|)

theorem quadraticLocalizationRadius_nonneg {P : ℝ} (hP : 0 ≤ P) (n : ℤ) :
    0 ≤ quadraticLocalizationRadius P n := by unfold quadraticLocalizationRadius; positivity

/-- The doubled-frequency bracket absorbs the single-frequency bracket. -/
theorem bracket_le_double_bracket_sq (n : ℤ) :
    1+|(n:ℝ)| ≤ (1+|((2*n:ℤ):ℝ)|)^2 := by
  simp only [Int.cast_mul, Int.cast_ofNat, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  nlinarith [abs_nonneg (n:ℝ), sq_nonneg |(n:ℝ)|]

/-- The explicit threshold bounds the diagonal by one eighth. -/
theorem quadratic_threshold_diagonal_le {P : ℝ} (n : ℤ) (hn : 8*P^2 ≤ 1+|(n:ℝ)|) :
    P^2/(1+|(n:ℝ)|) ≤ (1/8:ℝ) := by
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

/-- The off-diagonal product bound is at most one quarter, including n=0. -/
theorem quadratic_threshold_product_le {P : ℝ} (n : ℤ) (hn : 8*P^2 ≤ 1+|(n:ℝ)|) :
    2*P^2/(1+|((2*n:ℤ):ℝ)|)^2 ≤ (1/4:ℝ) := by
  apply (div_le_iff₀ (by positivity)).mpr
  linarith [bracket_le_double_bracket_sq n]

/-- The radius stays below 5/8 at the exact quadratic threshold. -/
theorem quadraticLocalizationRadius_le {P : ℝ} (hP : 0 ≤ P) (n : ℤ)
    (hn : 8*P^2 ≤ 1+|(n:ℝ)|) : quadraticLocalizationRadius P n ≤ 5/8 := by
  have hsq : (Real.sqrt 2*P)^2 ≤ ((1+|((2*n:ℤ):ℝ)|)/2)^2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [bracket_le_double_bracket_sq n]
  have hlin := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt 2*P)
    (by positivity : 0 ≤ (1+|((2*n:ℤ):ℝ)|)/2)).mp hsq
  have hoff : Real.sqrt 2*P/(1+|((2*n:ℤ):ℝ)|) ≤ (1/2:ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have ha := quadratic_threshold_diagonal_le n hn
  unfold quadraticLocalizationRadius
  linarith

/-- In particular the localization disc lies strictly inside radius π/5. -/
theorem quadraticLocalizationRadius_lt_pi_div_five {P : ℝ} (hP : 0 ≤ P) (n : ℤ)
    (hn : 8*P^2 ≤ 1+|(n:ℝ)|) : quadraticLocalizationRadius P n < Real.pi/5 := by
  exact (quadraticLocalizationRadius_le hP n hn).trans_lt (by linarith [Real.pi_gt_d2])

end NLS.ZakharovShabat
