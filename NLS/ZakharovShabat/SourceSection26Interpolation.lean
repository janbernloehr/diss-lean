import NLS.ZakharovShabat.SobolevJetInterpolation
import NLS.ZakharovShabat.SourcePiSobolevCoordinates

/-! # The valid ranges of (5.11) in the exact physical norm

The supremum bound holds for i<m, and the L² bound for i≤m. Both use
the physical weight 1+|2nπ|, with explicit constants.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- The exact physical weight dominates the auxiliary Sobolev coefficient norm. -/
theorem norm_sobolev_le_sourcePiSobolevScalar (m : ℕ) (a : ScalarSobolev m) :
    ‖a‖ ≤ ‖sourcePiSobolevScalar m m le_rfl a‖ := by
  change ‖WeightedCoeff.weightEquiv (Weight.sobolev m) 2 a‖ ≤ _
  apply lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0)
  intro n
  rw [WeightedCoeff.norm_weightEquiv_sobolev,sourcePiSobolevScalar_apply,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg ((SpectralWeight.piSobolev m (Nat.cast_nonneg m)).positive (2*n)).le]
  simp only [SpectralWeight.piSobolev_apply,Real.rpow_natCast,Int.cast_mul,Int.cast_ofNat,
    abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2),abs_of_pos Real.pi_pos]
  gcongr
  nlinarith [abs_nonneg (n:ℝ),Real.pi_gt_three]

/-- The supremum estimate (5.11) on its valid strict derivative range, with the physical Hᵐ norm. -/
theorem sourceSection26_supremum_interpolate (m i : ℕ) (hi : i < m) (a : ScalarSobolev m) :
    ‖hierarchySobolevJetContinuous m i hi a‖ ≤ 4*(2*Real.pi)^i*
      ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^(1-((i:ℝ)+1/2)/m)*
      ‖sourcePiSobolevScalar m m le_rfl a‖^(((i:ℝ)+1/2)/m) := by
  apply (norm_hierarchySobolevJetContinuous_interpolate m i hi a).trans
  gcongr
  exact norm_sobolev_le_sourcePiSobolevScalar m a

/-- The physical L² interpolation estimate includes the top derivative i=m. -/
theorem sourceSection26_L2_interpolate (m i : ℕ) (hm : 1 ≤ m) (hi : i ≤ m) (a : ScalarSobolev m) :
    ‖hierarchySobolevJetL2 m i hi a‖ ≤ (2*Real.pi)^i*
      ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^(1-(i:ℝ)/m)*
      ‖sourcePiSobolevScalar m m le_rfl a‖^((i:ℝ)/m) := by
  apply (norm_hierarchySobolevJetL2_interpolate m i hm hi a).trans
  gcongr
  exact norm_sobolev_le_sourcePiSobolevScalar m a

end NLS.ZakharovShabat
