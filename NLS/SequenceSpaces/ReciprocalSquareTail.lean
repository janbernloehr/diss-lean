import NLS.SequenceSpaces.ReciprocalSeries

/-! # A positive-index reciprocal-square tail budget -/

noncomputable section
namespace NLS.ReciprocalSeries

theorem summable_nat_reciprocal_sq_tail (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun k : ℕ => 1/((k : ℝ)+N)^2) := by
  have h := summable_nat_shifted_rpow
    (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega)) (by norm_num : (1 : ℝ) < 2)
  convert h using 1
  funext k
  rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]

theorem tsum_nat_reciprocal_sq_tail_le (N : ℕ) (hN : 1 ≤ N) :
    (∑' k : ℕ, 1/((k : ℝ)+N)^2) ≤ 2/(N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := tsum_nat_shifted_rpow_le hN' (by norm_num : (1 : ℝ) < 2)
  have he (k : ℕ) : ((k : ℝ)+N)^(-(2 : ℝ)) = 1/((k : ℝ)+N)^2 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
  simp only [he, show (1 : ℝ)-2 = -1 by norm_num, Real.rpow_neg_one,
    show (2 : ℝ)-1 = 1 by norm_num, div_one] at h
  rw [Real.rpow_neg hN'.le, Real.rpow_two] at h
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hi : ((N : ℝ)^2)⁻¹ ≤ (N : ℝ)⁻¹ := by
    exact inv_anti₀ hN' (by nlinarith)
  calc
    _ ≤ ((N : ℝ)^2)⁻¹+(N : ℝ)⁻¹ := h
    _ ≤ (N : ℝ)⁻¹+(N : ℝ)⁻¹ := add_le_add hi le_rfl
    _ = _ := by ring

end NLS.ReciprocalSeries
