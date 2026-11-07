import NLS.SequenceSpaces.HalfFourierEquiv

/-! Exact scalar normalization of the terminal polynomial in the native
signed minus-half Sobolev weight. Both signed modes use the same factor. -/
noncomputable section
open Complex
namespace NLS.WeightedCoeff

theorem signedHalf_terminal_normalization (n : ℕ+) (τ z : ℂ) :
    (Weight.signedSobolev (-1/2) ((n:ℕ):ℤ) : ℂ)*
      (2*τ*z/(((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ))) =
      ((Real.sqrt Real.pi : ℂ)/(Real.sqrt 2 : ℂ))*(τ/((Real.pi : ℂ)*(n:ℕ)))*z := by
  have hn : (0 : ℤ) < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
  have hnR : (0 : ℝ) < (n:ℕ) := by exact_mod_cast n.pos
  have hsπ : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hsn : (Real.sqrt (n:ℕ) : ℂ)^2 = (n:ℕ) := by
    exact_mod_cast Real.sq_sqrt hnR.le
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hns : (Real.sqrt (n:ℕ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hnR)
  rw [Weight.signedSobolev_positive (-1/2) _ hn,Weight.positiveSobolev_neg_half_positive]
  simp only [ofReal_div,ofReal_one,ofReal_mul,ofReal_ofNat]
  rw [← hsπ,← hsn]
  field_simp

theorem signedHalf_terminal_normalization_negative (n : ℕ+) (τ z : ℂ) :
    (Weight.signedSobolev (-1/2) (-((n:ℕ):ℤ)) : ℂ)*
      (2*τ*z/(((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ))) =
      ((Real.sqrt Real.pi : ℂ)/(Real.sqrt 2 : ℂ))*(τ/((Real.pi : ℂ)*(n:ℕ)))*z := by
  rw [Weight.signedSobolev_neg]
  exact signedHalf_terminal_normalization n τ z

/-- The native half-Fourier multiplier converts the actual first derivative
into the exact weighted signed terminal constant. -/
theorem signedHalf_halfFourier_derivative_normalization (n : ℕ+) (z : ℂ) :
    (Weight.signedSobolev (-1/2) ((n:ℕ):ℤ) : ℂ)*halfFourierSymbol ((n:ℕ):ℤ)*
      (2*I*(Real.pi : ℂ)*(n:ℕ)*z) =
        2*I*((Real.sqrt Real.pi : ℂ)/(Real.sqrt 2 : ℂ))*z := by
  have hn : (0 : ℤ) < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
  have hnR : (0 : ℝ) < (n:ℕ) := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ (n:ℕ) := by exact_mod_cast (Nat.succ_le_of_lt n.pos)
  have hsπ : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hsn : (Real.sqrt (n:ℕ) : ℂ)^2 = (n:ℕ) := by
    exact_mod_cast Real.sq_sqrt hnR.le
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hns : (Real.sqrt (n:ℕ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hnR)
  rw [Weight.signedSobolev_positive (-1/2) _ hn,Weight.positiveSobolev_neg_half_positive]
  unfold halfFourierSymbol
  simp only [Int.cast_natCast,abs_of_nonneg hnR.le,max_eq_right hn1]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [ofReal_div,ofReal_one,ofReal_mul]
  rw [← hsπ,← hsn]
  field_simp

theorem signedHalf_halfFourier_derivative_normalization_negative (n : ℕ+) (z : ℂ) :
    (Weight.signedSobolev (-1/2) (-((n:ℕ):ℤ)) : ℂ)*halfFourierSymbol (-((n:ℕ):ℤ))*
      (2*I*(Real.pi : ℂ)*(-((n:ℕ):ℤ))*z) =
        -2*I*((Real.sqrt Real.pi : ℂ)/(Real.sqrt 2 : ℂ))*z := by
  rw [Weight.signedSobolev_neg,halfFourierSymbol_neg]
  have h := signedHalf_halfFourier_derivative_normalization n (-z)
  simp only [Int.cast_natCast] at *
  linear_combination h

end NLS.WeightedCoeff
