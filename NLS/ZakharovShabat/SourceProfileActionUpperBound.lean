import NLS.ComplexAnalysis.SineCorrectionActionUpperBound
import NLS.ZakharovShabat.SourceGapActionLowerBound
import NLS.ZakharovShabat.SourceExteriorIndexDecay
import NLS.ZakharovShabat.SourceH1WeightedActionSequence
import NLS.ZakharovShabat.SourceSegmentCompactSeparation

/-! # Upper bounds from the actual gap profile

The finite-gap representation bounds the original action-to-gap ratio.
The exact exterior correction has inverse-square-bracket decay, uniformly
on each physical H1 ball and over all angles of every selected open gap.
The correction estimate itself has no finite-gap assumption.
-/

noncomputable section
open Set Metric Complex MeasureTheory
open scoped ENNReal

namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)
include A

/-- A uniform bound on the actual profile correction gives its sharp action upper bound. -/
theorem real_action_le_gap_sq_of_profile_upper
    (φ : realTypeSourceSubmodule p) (n : ℤ) (V : ℝ → ℝ) (hV : Continuous V)
    (E : ℝ) (hE : ∀ x ∈ Icc (0:ℝ) Real.pi, V x ≤ E)
    (hrep : ∀ x ∈ Icc (0:ℝ) Real.pi,
      sourceRealGapCosineProfile hp hp1 φ.val n x =
        (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re/2*
          Real.sin x*(1+V x)) :
    4*‖sourceComplexAction hp hp1 n φ.val‖ ≤
      (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re^2*(1+E) := by
  let g := (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
  let f := sourceRealGapCosineProfile hp hp1 φ.val n
  change ∀ x ∈ Icc (0:ℝ) Real.pi, f x = g/2*Real.sin x*(1+V x) at hrep
  have hfirst : ‖sourceComplexAction hp hp1 n φ.val‖ =
      g/Real.pi*(∫ x in (0:ℝ)..Real.pi, Real.sin x*f x) := by
    rw [← A.moment_one n (A.realType_subset_domain φ.property),A.real_moment_norm_eq_re φ n 1]
    simpa only [Nat.mul_zero,Nat.zero_add,pow_one,Complex.ofReal_re] using
      congrArg Complex.re (A.real_odd_moment_eq_cosineIntegral φ n 0)
  have ha : (∫ x in (0:ℝ)..Real.pi, Real.sin x*f x) =
      (g/2)*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*(1+V x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le Real.pi_pos.le] at hx
    dsimp only
    rw [hrep x hx]
    ring
  have he : ‖sourceComplexAction hp hp1 n φ.val‖ =
      g^2/(2*Real.pi)*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*(1+V x)) := by
    rw [hfirst,ha]
    ring
  have h := NLS.ComplexAnalysis.sine_correction_action_upper_bound V hV E g hE
  rw [he]
  change 4*(g^2/(2*Real.pi)*_) ≤ g^2*(1+E)
  linarith

/-- The actual finite-gap exterior correction controls the original action-to-gap ratio. -/
theorem real_action_le_gap_sq_of_exteriorCorrection_bound_finiteGap
    (φ : realTypeSourceSubmodule p) (n : ℤ) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (E : ℝ) (hE : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0 →
      ∀ x ∈ Icc (0:ℝ) Real.pi, sourceExteriorGapCorrection hp hp1 φ n x ≤ E) :
    4*‖sourceComplexAction hp hp1 n φ.val‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖^2*(1+E) := by
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _ (periodOnePotential_mem φ.val)
    (isRealType_periodOnePotential φ.val φ.property) n
  have hnorm : ‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖^2 =
      (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re^2 := by
    rw [Complex.sq_norm]
    simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,
      Complex.normSq_apply,Complex.sub_re,Complex.sub_im,him.1,him.2,sub_self,mul_zero,add_zero,pow_two]
  rw [hnorm]
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · rw [← A.moment_one n (A.realType_subset_domain φ.property),
      A.moment_of_collapsed φ.val (A.realType_subset_domain φ.property) n hg 1,hg]
    simp
  obtain ⟨V,_,_,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hcenter⟩ := hC φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  apply A.real_action_le_gap_sq_of_profile_upper φ n (sourceExteriorGapCorrection hp hp1 φ n)
    (continuous_sourceExteriorGapCorrection hp hp1 φ n hg (A.summable_actions_of_finiteGap φ hf)) E (hE hg)
  simpa only [sourceGapHalfWidthReal,canonicalPeriodicGap,Complex.sub_re] using
    C.real_profile_eq_actual_correction_finiteGap n φ hφ hf hg

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas

namespace NLS.ZakharovShabat

/-- One constant controls the actual exterior correction on each physical H1 ball. -/
theorem sourceExteriorGapCorrection_uniform_physical_H1_ball (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ n : ℤ, canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion a.val))
        (periodOnePotential_mem _) n ≠ 0 → ∀ θ : ℝ,
          (1+|(n:ℝ)|)^2*sourceExteriorGapCorrection (by simp) (by norm_num) (sourceH1RealSource a) n θ ≤ K := by
  obtain ⟨C,hC,hsep⟩ := exists_source_segment_index_separation_on_physical_H1_ball R
  obtain ⟨M,hM,hbound⟩ := exists_sourceH1WeightedActionSequence_bound_on_physical_ball R
  refine ⟨4*C^2*M,by positivity,?_⟩
  intro a ha n hg θ
  exact (sourceExteriorGapCorrection_weighted_bound (by simp) (by norm_num) (sourceH1RealSource a) C hC
    (hsep a ha) (sourceH1WeightedActionSequence a) (sourceH1WeightedActionSequence_density_majorant a) n hg θ).trans
      (mul_le_mul_of_nonneg_left (hbound a ha) (by positivity))

end NLS.ZakharovShabat
