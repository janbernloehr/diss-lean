import NLS.ZakharovShabat.SourceAngularBetaCompactBound
import NLS.ZakharovShabat.M1RealGlobalGapEstimate

/-! # Uniform inverse-bracket beta decay on physical H1 balls

The actual H1 gap sequence is bounded on each physical H1 ball by the
proved global M1 estimate. Combined with the compact off-diagonal beta
bound, this makes the full angular correction decay uniformly on the
ball. The original family is retained, without a finite-gap hypothesis.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- The existing global M1 estimate uniformly bounds the actual H1 gap sequence on physical H1 balls. -/
theorem exists_sourceH1WeightedGapSequence_bound_on_physical_ball (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ‖sourceH1WeightedGapSequence a.val‖ ≤ M := by
  let w := SpectralWeight.piSobolev 1 (by norm_num)
  let Q := 265*Real.pi^2*(w.realExtension (16*R^2))^2*(1+R^2)*R^2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨Real.sqrt Q,Real.sqrt_nonneg _,?_⟩
  intro a ha
  let φ := normalizedWeightedPeriodOne w (sourcePhysicalH1Coordinates a.val)
  have he : weightedBaseToPair w φ = periodOnePotential (sobolevSourceInclusion a.val) := by
    rw [weightedBaseToPair_normalizedWeightedPeriodOne]
    exact congrArg periodOnePotential (normalizedWeightedSource_physicalH1Coordinates a.val)
  have hev : weightedBaseToPair w φ ∈ pairParitySubspace 0 := by rw [he]; exact periodOnePotential_mem _
  have hr : IsRealType (weightedBaseToPair w φ) := by
    rw [he]; exact isRealType_periodOnePotential _ a.property
  obtain ⟨hs,hb⟩ := M1_real_canonicalGap_global_summable_and_le w
    (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl) φ hev hr
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
  have hG : ‖sourceH1WeightedGapSequence a.val‖^2 = ∑' n : ℤ, ‖sourceH1WeightedGapSequence a.val n‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) (sourceH1WeightedGapSequence a.val)
  have hGs : Summable (fun n : ℤ => ‖sourceH1WeightedGapSequence a.val n‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.memℓp (sourceH1WeightedGapSequence a.val)).summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)
  have hcomp (n : ℤ) : ‖sourceH1WeightedGapSequence a.val n‖^2 ≤
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) hev n‖)^2 := by
    simp only [he]
    change ‖((SpectralWeight.sobolev 1 (by norm_num)) (2*n):ℂ)*
      sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) n‖^2 ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg
      ((SpectralWeight.sobolev 1 (by norm_num)).positive _).le,sourcePeriodicGapDisplacement_apply]
    apply pow_le_pow_left₀ (mul_nonneg ((SpectralWeight.sobolev 1 (by norm_num)).positive _).le (norm_nonneg _))
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simp only [w,SpectralWeight.sobolev_apply,Weight.sobolev_apply,SpectralWeight.piSobolev_apply,Real.rpow_one]
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [abs_nonneg (((2*n:ℤ):ℝ)),Real.pi_gt_three]
  have hnorm := (hGs.tsum_le_tsum hcomp hs).trans hbR
  rw [← hG] at hnorm
  nlinarith [Real.sq_sqrt hQ,Real.sqrt_nonneg Q,norm_nonneg (sourceH1WeightedGapSequence a.val)]

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- Actual beta decay is uniform on each physical H1 ball, for the retained original family. -/
theorem betaCorrection_uniform_physical_H1_ball (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ n : ℤ, (1+|(n:ℝ)|)*‖sourceAngularBetaCorrection (by simp) (by norm_num) n s
        (sobolevSourceInclusion a.val)‖ ≤ K := by
  obtain ⟨C,hC,hβ⟩ := D.beta_uniform_physical_H1_ball R
  obtain ⟨M,hM,hG⟩ := exists_sourceH1WeightedGapSequence_bound_on_physical_ball R
  refine ⟨6*C*M,by positivity,?_⟩
  intro a ha n
  exact (sourceAngularBetaCorrection_weighted_bound s ⟨sobolevSourceInclusion a.val,a.property⟩
    (sourceH1WeightedGapSequence a.val) (sourceH1WeightedGapSequence_majorant a.val) C hC (hβ a ha) n).trans
      (mul_le_mul_of_nonneg_left (hG a ha) (by positivity))

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
