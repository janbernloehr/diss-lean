import NLS.SequenceSpaces.PositiveSobolevPowerComparison

/-! Reverse comparison with literal positive powers on [-1,1]. -/
noncomputable section
namespace NLS.Coeff

theorem sobolev_le_two_positive_power
    (r : ℝ) (hr0 : -1≤r) (hr1 : r≤1) (n : ℕ+) :
    Weight.sobolev r (n:ℤ)≤2*(n:ℝ)^r := by
  have h := positive_power_le_two_sobolev (-r) (by linarith) (by linarith) n
  have hn : (0:ℝ)<n := by exact_mod_cast n.pos
  have hw : Weight.sobolev (-r) (n:ℤ)=(Weight.sobolev r (n:ℤ))⁻¹ := by
    simp only [Weight.sobolev_apply,Real.rpow_neg (by positivity : (0:ℝ)≤1+|((n:ℤ):ℝ)|)]
  rw [Real.rpow_neg hn.le,hw] at h
  have hi : 1/(n:ℝ)^r≤2/Weight.sobolev r (n:ℤ) := by
    simpa only [one_div,div_eq_mul_inv,one_mul] using h
  simpa only [one_mul] using
    (div_le_div_iff₀ (Real.rpow_pos_of_pos hn r) ((Weight.sobolev r).positive (n:ℤ))).mp hi

end NLS.Coeff
