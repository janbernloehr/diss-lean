import NLS.ZakharovShabat.SobolevJetNormBounds

/-! # Separating the top derivative from the inhomogeneous Sobolev norm -/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The physical 2π normalization dominates the homogeneous Fourier moment. -/
theorem homogeneousMoment_le_highestJet_sq (m : ℕ) (a : ScalarSobolev m) :
    (∑' n : ℤ, |(n:ℝ)|^(2*(m:ℝ))*‖a.val n‖^2) ≤
      ‖hierarchySobolevJetL2 m m le_rfl a‖^2 := by
  have hJ : ‖hierarchySobolevJetL2 m m le_rfl a‖^2 =
      ∑' n : ℤ, ‖hierarchySobolevJetL2 m m le_rfl a n‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) (hierarchySobolevJetL2 m m le_rfl a)
  rw [hJ]
  apply (WeightedCoeff.summable_homogeneous (Nat.cast_nonneg m) a).tsum_le_tsum
  · intro n
    rw [hierarchySobolevJetL2_apply,norm_periodOneJetMultiplier,
      show 2*(m:ℝ)=((m*2:ℕ):ℝ) by push_cast; ring,Real.rpow_natCast,pow_mul]
    have hC : 1 ≤ (2*Real.pi)^m := one_le_pow₀ (by nlinarith [Real.pi_gt_three])
    have hb : |(n:ℝ)|^m*‖a.val n‖ ≤ (2*Real.pi)^m*|(n:ℝ)|^m*‖a.val n‖ := by
      simpa only [mul_assoc] using le_mul_of_one_le_left
        (mul_nonneg (pow_nonneg (abs_nonneg _) _) (norm_nonneg _)) hC
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hb 2
  · simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.memℓp (hierarchySobolevJetL2 m m le_rfl a)).summable (by norm_num)

/-- A quantitative bridge from H^m to the physical top derivative and L² norm. -/
theorem norm_sobolev_sq_le_highestJet (m : ℕ) (a : ScalarSobolev m) :
    ‖a‖^2 ≤ (2:ℝ)^(2*m)*(‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^2+
      ‖hierarchySobolevJetL2 m m le_rfl a‖^2) := by
  have h := WeightedCoeff.norm_sq_le_homogeneous (Nat.cast_nonneg m) a
  have he : (2:ℝ)^(2*(m:ℝ)) = (2:ℝ)^(2*m) := by
    rw [show 2*(m:ℝ)=((2*m:ℕ):ℝ) by push_cast; rfl,Real.rpow_natCast]
  rw [he] at h
  apply h.trans
  gcongr
  exact homogeneousMoment_le_highestJet_sq m a

end NLS.ZakharovShabat
