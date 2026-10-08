import NLS.ZakharovShabat.SobolevPhysicalJets
import NLS.SequenceSpaces.SobolevInterpolation

/-! # Exact-normalization bounds for physical Sobolev jets -/
noncomputable section
open NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The period-one derivative multiplier has exactly the expected magnitude. -/
theorem norm_periodOneJetMultiplier (k : ℕ) (n : ℤ) (z : ℂ) :
    ‖(2*Complex.I*(Real.pi:ℂ)*n)^k*z‖ = (2*Real.pi)^k*|(n:ℝ)|^k*‖z‖ := by
  simp [norm_pow,Complex.norm_intCast,mul_pow,mul_assoc,abs_of_pos Real.pi_pos]

private theorem norm_le_weighted (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) 2)
    (c : Coeff 2) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ C*(1+|(n:ℝ)|)^s*‖a.val n‖) : ‖c‖ ≤ C*‖a‖ := by
  have h := lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (x := c) (y := (C:ℂ) • WeightedCoeff.weightEquiv (Weight.sobolev s) 2 a) (fun n => ?_)
  · simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC,← WeightedCoeff.norm_eq] using h
  · change ‖c n‖ ≤ ‖(C:ℂ)*WeightedCoeff.weightEquiv (Weight.sobolev s) 2 a n‖
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hC,WeightedCoeff.norm_weightEquiv_sobolev]
    simpa only [mul_assoc] using hc n

/-- A k-th derivative costs exactly the factor (2π)^k in the H^k coefficient norm. -/
theorem norm_hierarchySobolevJetL2_le (s k : ℕ) (hk : k ≤ s) (a : ScalarSobolev s) :
    ‖hierarchySobolevJetL2 s k hk a‖ ≤ (2*Real.pi)^k*‖hierarchySobolevInclusion s k hk a‖ := by
  apply norm_le_weighted (k:ℝ) (hierarchySobolevInclusion s k hk a) _ _ (by positivity)
  intro n
  rw [hierarchySobolevJetL2_apply,norm_periodOneJetMultiplier,hierarchySobolevInclusion_apply,
    Real.rpow_natCast]
  gcongr
  linarith [abs_nonneg (n:ℝ)]

/-- The H¹ realization of a lower derivative costs (2π)^k in H^(k+1). -/
theorem norm_hierarchySobolevJet_H1_le (s k : ℕ) (hk : k < s) (a : ScalarSobolev s) :
    ‖hierarchySobolevToScalarDomain (s-k) (by omega) (hierarchySobolevJet s k (by omega) a)‖ ≤
      (2*Real.pi)^k*‖hierarchySobolevInclusion s (k+1) (by omega) a‖ := by
  let b := hierarchySobolevToScalarDomain (s-k) (by omega) (hierarchySobolevJet s k (by omega) a)
  change ‖WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 b‖ ≤ _
  apply norm_le_weighted ((k+1:ℕ):ℝ) (hierarchySobolevInclusion s (k+1) (by omega) a) _ _ (by positivity)
  intro n
  rw [WeightedCoeff.norm_weightEquiv_sobolev]
  simp only [b,hierarchySobolevToScalarDomain_apply,hierarchySobolevJet_apply,
    norm_periodOneJetMultiplier,hierarchySobolevInclusion_apply,Real.rpow_one,Real.rpow_natCast]
  calc
    _ ≤ (1+|(n:ℝ)|)*((2*Real.pi)^k*(1+|(n:ℝ)|)^k*‖a.val n‖) := by gcongr; linarith [abs_nonneg (n:ℝ)]
    _ = _ := by rw [pow_succ]; ring

/-- The L² derivative estimate in (5.11), with an explicit period-one constant. -/
theorem norm_hierarchySobolevJetL2_interpolate (m k : ℕ) (hm : 1 ≤ m) (hk : k ≤ m)
    (a : ScalarSobolev m) :
    ‖hierarchySobolevJetL2 m k hk a‖ ≤ (2*Real.pi)^k*
      ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^(1-(k:ℝ)/m)*‖a‖^((k:ℝ)/m) := by
  have h := WeightedCoeff.norm_sobolevInclusion_interpolate (m:ℝ) (k:ℝ)
    (by exact_mod_cast (show 0 < m by omega)) (Nat.cast_nonneg k) (by exact_mod_cast hk) a
  exact (norm_hierarchySobolevJetL2_le m k hk a).trans
    (by simpa only [mul_assoc,hierarchySobolevInclusion] using mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (2*Real.pi)^k))

end NLS.ZakharovShabat
