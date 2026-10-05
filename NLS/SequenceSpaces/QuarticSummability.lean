import NLS.SequenceSpaces.FunctionOrZero

/-! # Absolute summability from a quartic gap bound -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- A quartic majorant in `ℓ⁴` gives an absolute `ℓ¹` bound. -/
theorem summable_norm_of_quartic_bound (g : Coeff 4) (f : ℤ → ℂ) (B : ℝ)
    (hb : ∀ n, ‖f n‖ ≤ B*‖g n‖^4) :
    Summable (fun n => ‖f n‖) ∧ (∑' n, ‖f n‖) ≤ B*‖g‖^4 := by
  have hg : Summable (fun n => ‖g n‖^4) := by
    simpa using (lp.memℓp g).summable (by norm_num : 0 < (4:ℝ≥0∞).toReal)
  have hnorm : (∑' n, ‖g n‖^4) = ‖g‖^4 := by
    simpa using (lp.norm_rpow_eq_tsum (by norm_num : 0 < (4:ℝ≥0∞).toReal) g).symm
  have hs := (hg.mul_left B).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  refine ⟨hs,(hs.tsum_le_tsum hb (hg.mul_left B)).trans_eq ?_⟩
  rw [tsum_mul_left,hnorm]

/-- The total sequence constructor agrees with every quartically bounded coefficient. -/
theorem ofFunctionOrZero_one_apply_of_quartic_bound (g : Coeff 4) (f : ℤ → ℂ) (B : ℝ)
    (hb : ∀ n, ‖f n‖ ≤ B*‖g n‖^4) (n : ℤ) : ofFunctionOrZero 1 f n = f n := by
  apply ofFunctionOrZero_apply_of_mem
  apply memℓp_gen
  simpa using (summable_norm_of_quartic_bound g f B hb).1

/-- The realized `ℓ¹` sequence inherits the quartic norm bound. -/
theorem norm_ofFunctionOrZero_one_le_of_quartic_bound (g : Coeff 4) (f : ℤ → ℂ) (B : ℝ)
    (hb : ∀ n, ‖f n‖ ≤ B*‖g n‖^4) : ‖ofFunctionOrZero 1 f‖ ≤ B*‖g‖^4 := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
  simpa only [ENNReal.toReal_one,one_div_one,Real.rpow_one,
    ofFunctionOrZero_one_apply_of_quartic_bound g f B hb] using
      (summable_norm_of_quartic_bound g f B hb).2

end NLS.Coeff
