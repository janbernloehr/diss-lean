import NLS.ZakharovShabat.SourceWeightedGapSequence
import NLS.ZakharovShabat.SourcePiSobolevCoordinates
import NLS.ZakharovShabat.SourceHigherSobolevFiniteGapDensity
import NLS.ZakharovShabat.M1RealGlobalGapEstimate

/-! # Actual gap bounds on physical higher Sobolev balls

The actual weighted gap sequence has a uniform bound on every physical
Hm ball, for all integers m >= 1. The physical pair norms are monotone
when lowering the integer order, with their exact Fourier weights.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual weighted gap sequence at any integer Sobolev order. -/
def sourceHmWeightedGapSequence (m : ℕ) (a : SobolevSource m) : Coeff 2 :=
  sourceWeightedGapSequence (by simp) (by norm_num) (SpectralWeight.sobolev m (Nat.cast_nonneg m))
    (higherSobolevSourceInclusion m) (higherSobolevSourceWeightedPeriodOne m)
    (weightedBaseToPair_higherSobolevSourceWeightedPeriodOne m) a

theorem sourceHmWeightedGapSequence_majorant (m : ℕ) (a : SobolevSource m) (n : ℤ) :
    (1+|(n:ℝ)|)^m*‖sourcePeriodicGapDisplacement (by simp) (by norm_num)
      (higherSobolevSourceInclusion m a) n‖ ≤ ‖sourceHmWeightedGapSequence m a n‖ := by
  change _ ≤ ‖((SpectralWeight.sobolev m (Nat.cast_nonneg m)) (2*n):ℂ)*
    sourcePeriodicGapDisplacement (by simp) (by norm_num) (higherSobolevSourceInclusion m a) n‖
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg
    ((SpectralWeight.sobolev m (Nat.cast_nonneg m)).positive _).le]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simp only [SpectralWeight.sobolev_apply,Weight.sobolev_apply,Real.rpow_natCast,
    Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  apply pow_le_pow_left₀ (by positivity)
  linarith [abs_nonneg (n:ℝ)]

/-- Exact physical pair norms decrease when lowering the integer Sobolev order. -/
theorem norm_sourcePiSobolevCoordinates_mono (m k l : ℕ) (hk : k ≤ m) (hl : l ≤ m)
    (hkl : k ≤ l) (a : SobolevSource m) :
    ‖sourcePiSobolevCoordinates m k hk a‖ ≤ ‖sourcePiSobolevCoordinates m l hl a‖ := by
  have hs (c : ScalarSobolev m) :
      ‖sourcePiSobolevScalar m k hk c‖ ≤ ‖sourcePiSobolevScalar m l hl c‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro n
    simp only [sourcePiSobolevScalar_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_pos ((SpectralWeight.piSobolev k (Nat.cast_nonneg k)).positive _),
      abs_of_pos ((SpectralWeight.piSobolev l (Nat.cast_nonneg l)).positive _)]
    simp only [SpectralWeight.piSobolev_apply,Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith [abs_nonneg (((2*n:ℤ):ℝ)*Real.pi)]) hkl) (norm_nonneg _)
  have hk2 := norm_withLp_prod_rpow (p := 2) (by simp) (sourcePiSobolevCoordinates m k hk a)
  have hl2 := norm_withLp_prod_rpow (p := 2) (by simp) (sourcePiSobolevCoordinates m l hl a)
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two] at hk2 hl2
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hs a.1) 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (hs a.2) 2
  change ‖sourcePiSobolevCoordinates m k hk a‖^2 =
    ‖sourcePiSobolevScalar m k hk a.1‖^2+‖sourcePiSobolevScalar m k hk a.2‖^2 at hk2
  change ‖sourcePiSobolevCoordinates m l hl a‖^2 =
    ‖sourcePiSobolevScalar m l hl a.1‖^2+‖sourcePiSobolevScalar m l hl a.2‖^2 at hl2
  nlinarith [norm_nonneg (sourcePiSobolevCoordinates m k hk a),norm_nonneg (sourcePiSobolevCoordinates m l hl a)]

/-- The existing global M1 estimate uniformly bounds the actual Hm gap sequence on physical Hm balls. -/
theorem exists_sourceHmWeightedGapSequence_bound_on_physical_ball (m : ℕ) (hm : 1 ≤ m) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : realTypeHigherSobolevSourceLocus m, ‖sourcePiSobolevCoordinates m m le_rfl a.val‖ ≤ R →
      ‖sourceHmWeightedGapSequence m a.val‖ ≤ M := by
  let w := SpectralWeight.piSobolev m (Nat.cast_nonneg m)
  let Q := 265*Real.pi^2*(w.realExtension (16*R^2))^2*(1+R^2)*R^2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨Real.sqrt Q,Real.sqrt_nonneg _,?_⟩
  intro a ha
  let φ := normalizedWeightedPeriodOne w (sourcePiSobolevCoordinates m m le_rfl a.val)
  have he : weightedBaseToPair w φ = periodOnePotential (higherSobolevSourceInclusion m a.val) := by
    rw [weightedBaseToPair_normalizedWeightedPeriodOne]
    exact congrArg periodOnePotential (normalizedWeightedSource_sourcePiSobolevCoordinates m m le_rfl a.val)
  have hev : weightedBaseToPair w φ ∈ pairParitySubspace 0 := by rw [he]; exact periodOnePotential_mem _
  have hr : IsRealType (weightedBaseToPair w φ) := by
    rw [he]; exact isRealType_periodOnePotential _ a.property
  obtain ⟨hs,hb⟩ := M1_real_canonicalGap_global_summable_and_le w
    (SpectralWeight.hasLinearFactor_piSobolev m (by exact_mod_cast hm)) φ hev hr
  have hφ : ‖φ‖ ≤ R := by simpa only [φ,norm_normalizedWeightedPeriodOne] using ha
  have hR : 0 ≤ R := (norm_nonneg φ).trans hφ
  have hw : w.realExtension (16*‖φ‖^2) ≤ w.realExtension (16*R^2) := by
    apply w.realExtension_mono_abs
    rw [abs_of_nonneg (by positivity : 0 ≤ 16*‖φ‖^2),abs_of_nonneg (by positivity : 0 ≤ 16*R^2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg φ) hφ 2) (by positivity)
  have hbR : (∑' n : ℤ, (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num)
      (weightedBaseToPair w φ) hev n‖)^2) ≤ Q := hb.trans (by
    dsimp [Q]
    gcongr
    exact (w.realExtension_pos _).le)
  have hG : ‖sourceHmWeightedGapSequence m a.val‖^2 = ∑' n : ℤ, ‖sourceHmWeightedGapSequence m a.val n‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) (sourceHmWeightedGapSequence m a.val)
  have hGs : Summable (fun n : ℤ => ‖sourceHmWeightedGapSequence m a.val n‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.memℓp (sourceHmWeightedGapSequence m a.val)).summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)
  have hcomp (n : ℤ) : ‖sourceHmWeightedGapSequence m a.val n‖^2 ≤
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) hev n‖)^2 := by
    simp only [he]
    change ‖((SpectralWeight.sobolev m (Nat.cast_nonneg m)) (2*n):ℂ)*
      sourcePeriodicGapDisplacement (by simp) (by norm_num) (higherSobolevSourceInclusion m a.val) n‖^2 ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg
      ((SpectralWeight.sobolev m (Nat.cast_nonneg m)).positive _).le,sourcePeriodicGapDisplacement_apply]
    apply pow_le_pow_left₀ (mul_nonneg ((SpectralWeight.sobolev m (Nat.cast_nonneg m)).positive _).le (norm_nonneg _))
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simp only [w,SpectralWeight.sobolev_apply,Weight.sobolev_apply,SpectralWeight.piSobolev_apply,Real.rpow_natCast]
    rw [abs_mul,abs_of_pos Real.pi_pos]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [abs_nonneg (((2*n:ℤ):ℝ)),Real.pi_gt_three]
  have hnorm := (hGs.tsum_le_tsum hcomp hs).trans hbR
  rw [← hG] at hnorm
  nlinarith [Real.sq_sqrt hQ,Real.sqrt_nonneg Q,norm_nonneg (sourceHmWeightedGapSequence m a.val)]

end NLS.ZakharovShabat
