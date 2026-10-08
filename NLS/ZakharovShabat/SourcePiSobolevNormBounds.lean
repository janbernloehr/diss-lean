import NLS.ZakharovShabat.SourcePiSobolevCoordinates

/-! # Physical norm bounds used to sum the action estimates -/
noncomputable section
namespace NLS.ZakharovShabat

private theorem scalar_norm_le_piCoordinates (m k : ℕ) (hk : k ≤ m)
    (a : ScalarSobolev m) (b : Coeff 2)
    (h : ∀ n : ℤ, ‖b n‖ ≤ (1+2*Real.pi*|(n:ℝ)|)^k*‖a.val n‖) :
    ‖b‖ ≤ ‖sourcePiSobolevScalar m k hk a‖ := by
  apply lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0)
  intro n
  simp only [sourcePiSobolevScalar_apply, norm_mul, Complex.norm_real]
  rw [Real.norm_of_nonneg ((SpectralWeight.piSobolev k (Nat.cast_nonneg k)).positive (2*n)).le]
  simpa only [SpectralWeight.piSobolev_apply, Real.rpow_natCast, Int.cast_mul, Int.cast_ofNat,
    abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos Real.pi_pos,
    mul_right_comm (2:ℝ) |(n:ℝ)| Real.pi] using h n

/-- The physical mth derivative is controlled by the exact physical pair H^m norm. -/
theorem norm_highestJet_le_sourcePiSobolev (m : ℕ) (a : SobolevSource m) :
    ‖hierarchySobolevJetL2 m m le_rfl a.1‖ ≤ ‖sourcePiSobolevCoordinates m m le_rfl a‖ := by
  have h : ‖hierarchySobolevJetL2 m m le_rfl a.1‖ ≤ ‖sourcePiSobolevScalar m m le_rfl a.1‖ := by
    apply scalar_norm_le_piCoordinates
    intro n
    rw [hierarchySobolevJetL2_apply, norm_periodOneJetMultiplier, ← mul_pow]
    gcongr
    linarith
  exact h.trans (WithLp.norm_fst_le _ (sourcePiSobolevCoordinates m m le_rfl a))

/-- The scalar L² mass is bounded by the physical H¹ pair norm. -/
theorem norm_scalarMass_le_sourcePiSobolev_one (m : ℕ) (hm : 1 ≤ m) (a : SobolevSource m) :
    ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖ ≤
      ‖sourcePiSobolevCoordinates m 1 hm a‖ := by
  have h : ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖ ≤
      ‖sourcePiSobolevScalar m 1 hm a.1‖ := by
    apply scalar_norm_le_piCoordinates
    intro n
    rw [WeightedCoeff.sobolevToL2_apply, pow_one]
    have hp : 0 ≤ 2*Real.pi*|(n:ℝ)| := by positivity
    nlinarith [norm_nonneg (a.1.val n)]
  exact h.trans (WithLp.norm_fst_le _ (sourcePiSobolevCoordinates m 1 hm a))

/-- The scalar L² mass is one component of the original physical pair norm. -/
theorem norm_scalarMass_le_sourceMass (m : ℕ) (a : SobolevSource m) :
    ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖ ≤ ‖higherSobolevSourceInclusion m a‖ := by
  have he : WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1 =
      (higherSobolevSourceInclusion m a).fst := by
    ext n
    simp only [WeightedCoeff.sobolevToL2_apply, higherSobolevSourceInclusion_fst]
  rw [he]
  exact WithLp.norm_fst_le _ _

/-- The L²-only Hamiltonian error is absorbed by the H¹ remainder in Theorem 23.2(i). -/
theorem source_scalarMass_remainder_le (m : ℕ) (hm : 1 ≤ m) (a : SobolevSource m) :
    (1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖^(4*m))*
      ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖^2 ≤
      2*(1+‖sourcePiSobolevCoordinates m 1 hm a‖)^(4*m)*‖higherSobolevSourceInclusion m a‖^2 := by
  have ha := norm_scalarMass_le_sourcePiSobolev_one m hm a
  have hb := norm_scalarMass_le_sourceMass m a
  have hone : 1 ≤ (1+‖sourcePiSobolevCoordinates m 1 hm a‖)^(4*m) :=
    one_le_pow₀ (by linarith [norm_nonneg (sourcePiSobolevCoordinates m 1 hm a)])
  have hp : ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖^(4*m) ≤
      (1+‖sourcePiSobolevCoordinates m 1 hm a‖)^(4*m) :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc
    _ ≤ (2*(1+‖sourcePiSobolevCoordinates m 1 hm a‖)^(4*m))*
        ‖higherSobolevSourceInclusion m a‖^2 :=
      mul_le_mul (by linarith) hs (by positivity) (by positivity)
    _ = _ := rfl

end NLS.ZakharovShabat
