import NLS.ZakharovShabat.SourcePiSobolevCoordinates

/-! # The physical norm splitting in the proof of Lemma 26.3 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- The scalar physical Sobolev norm is exactly its weighted Fourier energy. -/
theorem sourcePiSobolevScalar_norm_sq (m : ℕ) (a : ScalarSobolev m) :
    ‖sourcePiSobolevScalar m m le_rfl a‖^2 =
      ∑' n : ℤ, (1+2*Real.pi*|(n:ℝ)|)^(2*m)*‖a.val n‖^2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ENNReal).toReal)
    (sourcePiSobolevScalar m m le_rfl a)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at h
  rw [h]
  apply tsum_congr
  intro n
  rw [sourcePiSobolevScalar_apply,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg ((SpectralWeight.piSobolev m (Nat.cast_nonneg m)).positive (2*n)).le]
  simp only [SpectralWeight.piSobolev_apply,Real.rpow_natCast,mul_pow,← pow_mul,
    Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),
    abs_of_pos Real.pi_pos]
  congr 2 <;> ring

/-- A direct corrected splitting with the exact physical weight 1+|2nπ|.
The same bound includes the zero-order endpoint. -/
theorem sourceSection26_physicalNorm_split (m : ℕ) (a : ScalarSobolev m) :
    ‖sourcePiSobolevScalar m m le_rfl a‖^2 ≤ (2:ℝ)^(2*m-1)*
      (‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^2+
        ‖hierarchySobolevJetL2 m m le_rfl a‖^2) := by
  have energy (c : Coeff 2) : ‖c‖^2 = ∑' n : ℤ, ‖c n‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ENNReal).toReal) c
  have summable_energy (c : Coeff 2) : Summable (fun n : ℤ => ‖c n‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.memℓp c).summable (by norm_num : 0 < (2:ENNReal).toReal)
  let L := WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a
  let J := hierarchySobolevJetL2 m m le_rfl a
  have hs : Summable (fun n : ℤ => (1+2*Real.pi*|(n:ℝ)|)^(2*m)*‖a.val n‖^2) := by
    convert summable_energy (sourcePiSobolevScalar m m le_rfl a) using 1
    ext n
    rw [sourcePiSobolevScalar_apply,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg ((SpectralWeight.piSobolev m (Nat.cast_nonneg m)).positive (2*n)).le]
    simp only [SpectralWeight.piSobolev_apply,Real.rpow_natCast,mul_pow,← pow_mul,
      Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),
      abs_of_pos Real.pi_pos]
    congr 2 <;> ring
  rw [sourcePiSobolevScalar_norm_sq]
  calc
    _ ≤ ∑' n : ℤ, (2:ℝ)^(2*m-1)*(‖L n‖^2+‖J n‖^2) := by
      apply hs.tsum_le_tsum _ (((summable_energy L).add (summable_energy J)).mul_left _)
      intro n
      have hb := mul_le_mul_of_nonneg_right
        (add_pow_le (by norm_num : (0:ℝ)≤1) (by positivity : 0≤2*Real.pi*|(n:ℝ)|) (2*m))
        (sq_nonneg ‖a.val n‖)
      dsimp only [L,J]
      rw [WeightedCoeff.sobolevToL2_apply,hierarchySobolevJetL2_apply,
        norm_periodOneJetMultiplier]
      convert hb using 1
      ring
    _ = _ := by
      rw [tsum_mul_left,(summable_energy L).tsum_add (summable_energy J),← energy L,← energy J]

end NLS.ZakharovShabat
