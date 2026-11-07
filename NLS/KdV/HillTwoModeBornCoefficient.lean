import NLS.KdV.HillWideTwoModeOperator

/-! The exact second Born coefficient for the symmetric near-resonant
potential supported at ±(2n-2), evaluated at the free spectral center. -/
noncomputable section
namespace NLS.KdV

theorem wideHillSymbol_twoMode_center_sum (n : ℕ) (hn : 3 ≤ n) :
    wideHillSymbol n (freeHillValue n:ℂ) ((n:ℤ)-(2*(n:ℤ)-2))+
      wideHillSymbol n (freeHillValue n:ℂ) ((n:ℤ)+(2*(n:ℤ)-2)) =
        (((2*Real.pi^2*(2*(n:ℝ)-1))⁻¹:ℝ):ℂ) := by
  have h₁ : ((n:ℤ)-(2*(n:ℤ)-2)).natAbs ≠ n := by omega
  have h₂ : ((n:ℤ)+(2*(n:ℤ)-2)).natAbs ≠ n := by omega
  have hN : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hA : (n:ℂ)-1 ≠ 0 := by
    have : (n:ℝ)-1 ≠ 0 := by linarith
    exact_mod_cast this
  have hB : 2*(n:ℂ)-1 ≠ 0 := by
    have : 2*(n:ℝ)-1 ≠ 0 := by linarith
    exact_mod_cast this
  have he₁ : (freeHillValue n:ℂ)-(freeHillValue ((n:ℤ)-(2*(n:ℤ)-2)):ℂ) =
      4*(Real.pi:ℂ)^2*((n:ℂ)-1) := by
    simp only [freeHillValue]
    push_cast
    ring
  have he₂ : (freeHillValue n:ℂ)-(freeHillValue ((n:ℤ)+(2*(n:ℤ)-2)):ℂ) =
      -4*(Real.pi:ℂ)^2*(2*(n:ℂ)-1)*((n:ℂ)-1) := by
    simp only [freeHillValue]
    push_cast
    ring
  rw [wideHillSymbol,if_neg h₁,wideHillSymbol,if_neg h₂,he₁,he₂]
  push_cast
  have hB' : -1+(n:ℂ)*2 ≠ 0 := by
    convert hB using 1; ring
  field_simp [hπ,hA,hB,hB']
  linear_combination -2*(mul_inv_cancel₀ hB')

theorem wideHillSymbol_twoMode_center_sum_lower (n : ℕ) (hn : 3 ≤ n) :
    1/(64*(n:ℝ)) ≤
      ‖wideHillSymbol n (freeHillValue n:ℂ) ((n:ℤ)-(2*(n:ℤ)-2))+
        wideHillSymbol n (freeHillValue n:ℂ) ((n:ℤ)+(2*(n:ℤ)-2))‖ := by
  have hN : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hB : 0<2*(n:ℝ)-1 := by
    have : (3:ℝ)≤n := by exact_mod_cast hn
    linarith
  rw [wideHillSymbol_twoMode_center_sum n hn,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  have hπ : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
  rw [one_div]
  change (64*(n:ℝ))⁻¹ ≤ (2*Real.pi^2*(2*(n:ℝ)-1))⁻¹
  apply inv_anti₀ (by positivity)
  have := mul_le_mul_of_nonneg_right hπ hB.le
  nlinarith [sq_nonneg Real.pi]

end NLS.KdV
