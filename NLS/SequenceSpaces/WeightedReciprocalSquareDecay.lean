import NLS.SequenceSpaces.WeightedReciprocalDecay

/-! # Inverse-square-bracket decay of reciprocal-square sums

A two-derivative l1 majorant controls the entire punctured reciprocal-square
sum, uniformly at every signed selected index, including zero.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- A reciprocal-square row transfers a full squared bracket with constant four. -/
theorem weighted_punctured_row_sq_le (n m : ℤ) :
    (1+|(n:ℝ)|)^2*‖shift n (puncturedLattice 2 (by norm_num)) m‖^2 ≤ 4*(1+|(m:ℝ)|)^2 := by
  have hb : ‖shift n (puncturedLattice 2 (by norm_num)) m‖ ≤ 1 := by
    rw [norm_shift_puncturedLattice_apply]
    split_ifs with hm
    · norm_num
    · apply inv_le_one_of_one_le₀
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hm)
  have hd : ‖shiftedInverse 1 le_rfl m‖ ≤ 1 := by
    rw [shiftedInverse_apply,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1+|(m:ℝ)|)]
    exact inv_le_one_of_one_le₀ (by linarith [abs_nonneg (m:ℝ)])
  have h := (weighted_punctured_row_le n m).trans
    (mul_le_mul_of_nonneg_left (show ‖shift n (puncturedLattice 2 (by norm_num)) m‖+
      ‖shiftedInverse 1 le_rfl m‖ ≤ 2 by linarith) (by positivity))
  have hs := pow_le_pow_left₀ (show 0 ≤ (1+|(n:ℝ)|)*‖shift n (puncturedLattice 2 (by norm_num)) m‖ by positivity) h 2
  nlinarith

/-- A two-derivative l1 majorant gives inverse-square-bracket decay of the full sum. -/
theorem summable_norm_reciprocal_sq_of_weighted_l1 (a : Coeff 1) (u : ℤ → ℂ)
    (n : ℤ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ m, ‖u m‖ ≤ C*‖a m‖/(1+|(m:ℝ)|)^2*
      ‖shift n (puncturedLattice 2 (by norm_num)) m‖^2) :
    Summable (fun m => ‖u m‖) ∧
      (1+|(n:ℝ)|)^2*(∑' m, ‖u m‖) ≤ 4*C*‖a‖ := by
  let M := fun m : ℤ => 4*C*‖a m‖
  have hMs : Summable M := ((lp.memℓp a).norm.summable_of_one).mul_left (4*C)
  have hdom (m : ℤ) : (1+|(n:ℝ)|)^2*‖u m‖ ≤ M m := by
    have h := mul_le_mul_of_nonneg_left (weighted_punctured_row_sq_le n m)
      (show 0 ≤ C*‖a m‖/(1+|(m:ℝ)|)^2 by positivity)
    calc
      _ ≤ (1+|(n:ℝ)|)^2*(C*‖a m‖/(1+|(m:ℝ)|)^2*
          ‖shift n (puncturedLattice 2 (by norm_num)) m‖^2) :=
        mul_le_mul_of_nonneg_left (hu m) (by positivity)
      _ = C*‖a m‖/(1+|(m:ℝ)|)^2*((1+|(n:ℝ)|)^2*
          ‖shift n (puncturedLattice 2 (by norm_num)) m‖^2) := by ring
      _ ≤ C*‖a m‖/(1+|(m:ℝ)|)^2*(4*(1+|(m:ℝ)|)^2) := h
      _ = M m := by dsimp [M];field_simp
  have hs := hMs.of_nonneg_of_le (fun m => by positivity) hdom
  have hus : Summable (fun m => ‖u m‖) := by
    have h := hs.mul_left ((1+|(n:ℝ)|)^2)⁻¹
    simpa only [← mul_assoc,inv_mul_cancel₀ (by positivity : (1+|(n:ℝ)|)^2 ≠ 0),one_mul] using h
  refine ⟨hus,?_⟩
  have hsum := hs.tsum_le_tsum hdom hMs
  have he : (∑' m : ℤ, ‖a m‖) = ‖a‖ := by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using (lp.norm_rpow_eq_tsum (by simp) a).symm
  simpa only [M,tsum_mul_left,he] using hsum

end NLS.Coeff