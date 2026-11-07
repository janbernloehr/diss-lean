import NLS.ComplexAnalysis.PairedPoleNormalizedFactor

/-! The exact quadratic spectral map converts a squared frequency-gap
offset into the original squared energy-gap divided by its positive
index. No asymptotic normalization of the numerator is used. -/
noncomputable section
open Complex
namespace NLS.KdV

theorem norm_quadratic_energy_offset_le (β τ γ : ℂ) (m : ℕ+) (a B L : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hoffset : ‖β-τ‖ ≤ L*‖γ‖^2) (hlower : a*(m:ℝ) ≤ ‖τ‖) (hupper : ‖β+τ‖ ≤ B*(m:ℝ)) :
    ‖β^2-τ^2-γ^2/4‖ ≤ ((L*B+1)/(4*a^2))*‖γ^2*(2*τ)^2‖/(m:ℝ) := by
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast m.pos
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast m.property
  let D := (L*B+1)/(4*a^2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hcoarse : ‖β^2-τ^2-γ^2/4‖ ≤ (L*B+1)*(m:ℝ)*‖γ‖^2 := by
    rw [show β^2-τ^2-γ^2/4 = (β-τ)*(β+τ)-γ^2/4 by ring]
    calc
      _ ≤ ‖(β-τ)*(β+τ)‖+‖γ^2/4‖ := norm_sub_le _ _
      _ = ‖β-τ‖*‖β+τ‖+‖γ‖^2/4 := by rw [norm_mul,norm_div,norm_pow,Complex.norm_ofNat]
      _ ≤ (L*‖γ‖^2)*(B*(m:ℝ))+‖γ‖^2/4 := add_le_add
        (mul_le_mul hoffset hupper (norm_nonneg _) (by positivity)) le_rfl
      _ ≤ (L*B+1)*(m:ℝ)*‖γ‖^2 := by nlinarith [sq_nonneg ‖γ‖]
  have hsq : a^2*(m:ℝ)^2 ≤ ‖τ‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg ha.le hmpos.le) hlower 2
  have hgap : 4*a^2*(m:ℝ)^2*‖γ‖^2 ≤ ‖γ^2*(2*τ)^2‖ := by
    simp only [norm_mul,norm_pow,Complex.norm_ofNat]
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖γ‖)]
  apply (le_div_iff₀ hmpos).mpr
  calc
    _ ≤ ((L*B+1)*(m:ℝ)*‖γ‖^2)*(m:ℝ) := mul_le_mul_of_nonneg_right hcoarse hmpos.le
    _ = D*(4*a^2*(m:ℝ)^2*‖γ‖^2) := by dsimp only [D]; field_simp
    _ ≤ D*‖γ^2*(2*τ)^2‖ := mul_le_mul_of_nonneg_left hgap hD

end NLS.KdV
