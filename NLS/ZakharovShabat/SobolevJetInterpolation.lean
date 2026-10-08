import NLS.ZakharovShabat.SobolevJetNormBounds
import NLS.SequenceSpaces.HilbertAgmon

/-! # The physical supremum interpolation inequality (5.11)

The multiplicative H¹ embedding applied to the k-th derivative, followed by
Hilbert interpolation at orders k and k+1, yields the exact exponent
(k+1/2)/m. All constants retain the period-one Fourier normalization.
-/
noncomputable section
open scoped ENNReal
open NLS.Fourier MeasureTheory
namespace NLS.ZakharovShabat

/-- The uniform derivative norm is controlled by adjacent Hilbert norms. -/
theorem norm_hierarchySobolevJetContinuous_sq_le (m k : ℕ) (hk : k < m) (a : ScalarSobolev m) :
    ‖hierarchySobolevJetContinuous m k hk a‖^2 ≤ 12*
      ‖hierarchySobolevJetL2 m k (by omega) a‖*
      ‖hierarchySobolevToScalarDomain (m-k) (by omega) (hierarchySobolevJet m k (by omega) a)‖ := by
  let c := hierarchySobolevToScalarDomain (m-k) (by omega) (hierarchySobolevJet m k (by omega) a)
  have he : WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ) ≤ 1) c =
      hierarchySobolevJetL2 m k (by omega) a := by
    ext n
    simp only [c,WeightedCoeff.sobolevToL2_apply,hierarchySobolevToScalarDomain_apply,
      hierarchySobolevJet_apply,hierarchySobolevJetL2_apply]
  have hsyn : ‖hierarchySobolevJetContinuous m k hk a‖ ≤
      ‖WeightedCoeff.sobolevToL1CLM 2 (by simp) c‖ := by
    change ‖continuousSynthesis (Coeff.periodDouble (WeightedCoeff.sobolevToL1CLM 2 (by simp) c))‖ ≤ _
    simpa only [Coeff.periodDouble.norm_map] using
      norm_continuousSynthesis_le (Coeff.periodDouble (WeightedCoeff.sobolevToL1CLM 2 (by simp) c))
  exact (pow_le_pow_left₀ (norm_nonneg _) hsyn 2).trans
    (by simpa only [he] using WeightedCoeff.norm_sobolevToL1_sq_le c)

private theorem geometric_product (A B u v : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    (A^(1-u)*B^u)*(A^(1-v)*B^v) = A^(2-(u+v))*B^(u+v) := by
  rw [mul_mul_mul_comm,← Real.rpow_add_of_nonneg hA (sub_nonneg.mpr hu1) (sub_nonneg.mpr hv1),
    ← Real.rpow_add_of_nonneg hB hu hv]
  congr 2
  ring

/-- The sharp supremum exponent of (5.11), with an explicit constant 4(2π)^k. -/
theorem norm_hierarchySobolevJetContinuous_interpolate (m k : ℕ) (hk : k < m) (a : ScalarSobolev m) :
    ‖hierarchySobolevJetContinuous m k hk a‖ ≤ 4*(2*Real.pi)^k*
      ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^(1-((k:ℝ)+1/2)/m)*
      ‖a‖^(((k:ℝ)+1/2)/m) := by
  have hm : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  let A := ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖
  let B := ‖a‖
  let C := (2*Real.pi)^k
  let u : ℝ := k/m
  let v : ℝ := (k+1:ℕ)/m
  let t : ℝ := ((k:ℝ)+1/2)/m
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu1 : u ≤ 1 := (div_le_one hm).mpr (by exact_mod_cast hk.le)
  have hv1 : v ≤ 1 := (div_le_one hm).mpr (by exact_mod_cast (show k+1 ≤ m by omega))
  have ht : 2*t = u+v := by dsimp [t,u,v]; push_cast; ring
  have hL : ‖hierarchySobolevJetL2 m k (by omega) a‖ ≤ C*(A^(1-u)*B^u) := by
    simpa only [C,A,B,u,mul_assoc] using norm_hierarchySobolevJetL2_interpolate m k (by omega) (by omega) a
  have hH : ‖hierarchySobolevToScalarDomain (m-k) (by omega) (hierarchySobolevJet m k (by omega) a)‖ ≤
      C*(A^(1-v)*B^v) := by
    apply (norm_hierarchySobolevJet_H1_le m k hk a).trans
    have hi := WeightedCoeff.norm_sobolevInclusion_interpolate (m:ℝ) ((k+1:ℕ):ℝ) hm
      (Nat.cast_nonneg _) (by exact_mod_cast (show k+1 ≤ m by omega)) a
    exact mul_le_mul_of_nonneg_left hi (by positivity)
  have hs : ‖hierarchySobolevJetContinuous m k hk a‖^2 ≤
      12*C^2*(A^(2-(u+v))*B^(u+v)) := by
    apply (norm_hierarchySobolevJetContinuous_sq_le m k hk a).trans
    calc
      _ ≤ 12*(C*(A^(1-u)*B^u))*(C*(A^(1-v)*B^v)) := by gcongr
      _ = _ := by rw [← geometric_product A B u v (norm_nonneg _) (norm_nonneg _) hu hu1 hv hv1]; ring
  have hsq : (4*C*A^(1-t)*B^t)^2 = 16*C^2*(A^(2-(u+v))*B^(u+v)) := by
    rw [mul_pow,mul_pow,mul_pow,← Real.rpow_mul_natCast (norm_nonneg _),
      ← Real.rpow_mul_natCast (norm_nonneg _)]
    norm_num only [Nat.cast_ofNat,show (4:ℝ)^2=16 by norm_num]
    rw [show (1-t)*2 = 2-(u+v) by linarith,show t*2 = u+v by linarith]
    ring
  have hp : 0 ≤ C^2*(A^(2-(u+v))*B^(u+v)) := by positivity
  have hn : 0 ≤ 4*C*A^(1-t)*B^t := by positivity
  change ‖hierarchySobolevJetContinuous m k hk a‖ ≤ 4*C*A^(1-t)*B^t
  nlinarith [norm_nonneg (hierarchySobolevJetContinuous m k hk a)]

/-- Pointwise form of the supremum interpolation estimate on the actual physical interval. -/
theorem norm_hierarchySobolevJetContinuous_apply_interpolate (m k : ℕ) (hk : k < m)
    (a : ScalarSobolev m) (x : ℝ) :
    ‖hierarchySobolevJetContinuous m k hk a (x : AddCircle (2:ℝ))‖ ≤ 4*(2*Real.pi)^k*
      ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^(1-((k:ℝ)+1/2)/m)*
      ‖a‖^(((k:ℝ)+1/2)/m) :=
  ((hierarchySobolevJetContinuous m k hk a).norm_coe_le_norm _).trans
    (norm_hierarchySobolevJetContinuous_interpolate m k hk a)

/-- Parseval identifies every lower jet's actual physical L² energy with its
Fourier norm. This supplies the two L² factors in the monomial estimate (5.12). -/
theorem integral_norm_sq_hierarchySobolevJetContinuous (m k : ℕ) (hk : k < m)
    (a : ScalarSobolev m) :
    (∫ x in (0:ℝ)..1, ‖hierarchySobolevJetContinuous m k hk a (x : AddCircle (2:ℝ))‖^2) =
      ‖hierarchySobolevJetL2 m k (by omega) a‖^2 := by
  let c := hierarchySobolevToScalarDomain (m-k) (by omega) (hierarchySobolevJet m k (by omega) a)
  let f := fun x : ℝ => periodOneSobolevSynthesis c (x : AddCircle (2:ℝ))
  have h := hasSum_sq_fourierCoeffOn (by norm_num : (0:ℝ) < 1)
    (memLp_two_interval (continuous_periodOneSobolevSynthesis c) 0 1 (by norm_num))
  have hc (n : ℤ) : fourierCoeffOn (by norm_num : (0:ℝ) < 1) f n =
      hierarchySobolevJetL2 m k (by omega) a n := by
    change periodOneCoefficient f n = _
    simp only [f,periodOneCoefficient_periodOneSobolevSynthesis,c,
      hierarchySobolevToScalarDomain_apply,hierarchySobolevJet_apply,hierarchySobolevJetL2_apply]
  change HasSum (fun n => ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) f n‖^2) _ at h
  simp only [hc,sub_zero,inv_one,one_smul] at h
  have hJ : HasSum (fun n : ℤ => ‖hierarchySobolevJetL2 m k (by omega) a n‖^2)
      (‖hierarchySobolevJetL2 m k (by omega) a‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.hasSum_norm (by norm_num : 0 < (2:ℝ≥0∞).toReal) (hierarchySobolevJetL2 m k (by omega) a)
  exact h.unique hJ

end NLS.ZakharovShabat
