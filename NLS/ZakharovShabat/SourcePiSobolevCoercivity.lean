import NLS.ZakharovShabat.HigherSobolevH1Realization
import NLS.ZakharovShabat.OddHamiltonianRemainderEstimate

/-! # Recovering the exact physical Sobolev norm from the highest derivative -/
noncomputable section
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- The physical Fourier rescaling has an explicit norm bound. -/
theorem norm_sourcePiSobolevScalar_le (m k : ℕ) (hk : k ≤ m) (a : ScalarSobolev m) :
    ‖sourcePiSobolevScalar m k hk a‖ ≤ (2*Real.pi)^k*‖a‖ := by
  unfold sourcePiSobolevScalar
  rw [← WeightedCoeff.norm_eq]
  exact WeightedCoeff.norm_weightedMultiplier_le _ _ _ _ (by positivity) _ _

/-- Conjugate reflection preserves every physical Sobolev weight. -/
theorem sourcePiSobolevCoordinates_norm_sq_eq_twice_fst (m k : ℕ) (hk : k ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    ‖sourcePiSobolevCoordinates m k hk a.val‖^2 =
      2*‖sourcePiSobolevScalar m k hk a.val.1‖^2 := by
  have he : (sourcePiSobolevCoordinates m k hk a.val).snd =
      star (Coeff.reflection (sourcePiSobolevCoordinates m k hk a.val).fst) := by
    ext n
    change _ = conj ((sourcePiSobolevCoordinates m k hk a.val).fst (-n))
    rw [sourcePiSobolevCoordinates_snd,sourcePiSobolevCoordinates_fst,
      realTypeHigherSobolevSource_coefficients]
    simp only [SpectralWeight.piSobolev_apply,mul_neg,Int.cast_neg,neg_mul,abs_neg,
      map_mul,Complex.conj_ofReal]
  rw [WithLp.prod_norm_sq_eq_of_L2,he,norm_star,Coeff.reflection.norm_map]
  change ‖sourcePiSobolevScalar m k hk a.val.1‖^2+
    ‖sourcePiSobolevScalar m k hk a.val.1‖^2 = _
  ring

/-- A uniform bridge for the exact physical pair norm. -/
theorem sourcePiSobolev_norm_sq_le_mass_add_highestJet (m : ℕ)
    (a : realTypeHigherSobolevSourceLocus m) :
    ‖sourcePiSobolevCoordinates m m le_rfl a.val‖^2 ≤
      (2*(2*Real.pi)^(2*m)*2^(2*m))*
        (‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^2+
          ‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2) := by
  rw [sourcePiSobolevCoordinates_norm_sq_eq_twice_fst]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sourcePiSobolevScalar_le m m le_rfl a.val.1) 2
  rw [mul_pow,← pow_mul, Nat.mul_comm m 2] at h
  have hj := mul_le_mul_of_nonneg_left (norm_sobolev_sq_le_highestJet m a.val.1)
    (by positivity : 0 ≤ (2*Real.pi)^(2*m))
  nlinarith

/-- The total original action is exactly the scalar L² energy. -/
theorem sourceHigher_sum_actions_eq_scalar_mass (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n) =
      ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^2 := by
  have h := sourceH1_sum_actions_eq_mass (realHigherSobolevToH1 m hm a)
  rw [sourceH1RealSource_realHigherSobolevToH1,
    periodOneSobolevMass_real_eq (realHigherSobolevToH1 m hm a),Complex.ofReal_re] at h
  have he : scalarInclusion (higherSobolevToH1 m hm a.val).1 =
      WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1 := by
    ext n
    simp [higherSobolevToH1]
  change _ = ‖scalarInclusion (higherSobolevToH1 m hm a.val).1‖^2 at h
  rwa [he] at h

end NLS.ZakharovShabat
