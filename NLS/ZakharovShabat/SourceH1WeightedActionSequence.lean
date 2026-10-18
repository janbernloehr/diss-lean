import NLS.ZakharovShabat.SourceH1ActionSums
import NLS.ZakharovShabat.SourceSection28Asymptotics
import NLS.ZakharovShabat.SourceGapAngularDensity

/-! # The exact physical H1 weighted action sequence

The physical weighted actions form an l1 sequence whose norm is their
literal sum. This sequence majorizes the actual angular-density masses
and is uniformly bounded on every physical H1 ball.
-/

noncomputable section
open Set Metric Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The exact physical bracket-weighted real actions as an l1 sequence. -/
def sourceH1WeightedActionSequence (a : realTypeSobolevSourceLocus) : Coeff 1 :=
  ⟨fun n => (sourceWeightedActionTerm (sourceH1RealSource a) 1 n : ℂ),by
    have hn (n : ℤ) : 0 ≤ sourceWeightedActionTerm (sourceH1RealSource a) 1 n := by
      dsimp [sourceWeightedActionTerm]; positivity
    change Memℓp (fun n => (sourceWeightedActionTerm (sourceH1RealSource a) 1 n : ℂ)) 1
    rw [memℓp_gen_iff (by simp : 0 < (1:ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_one,Real.rpow_one,Complex.norm_real,Real.norm_of_nonneg (hn _)] using
      sourceH1_weightedActions_summable a⟩

@[simp] theorem sourceH1WeightedActionSequence_apply (a : realTypeSobolevSourceLocus) (n : ℤ) :
    sourceH1WeightedActionSequence a n = (sourceWeightedActionTerm (sourceH1RealSource a) 1 n : ℂ) := rfl

/-- The sequence norm is the literal physical weighted action sum. -/
theorem norm_sourceH1WeightedActionSequence (a : realTypeSobolevSourceLocus) :
    ‖sourceH1WeightedActionSequence a‖ = ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n := by
  have hn (n : ℤ) : 0 ≤ sourceWeightedActionTerm (sourceH1RealSource a) 1 n := by
    dsimp [sourceWeightedActionTerm]; positivity
  simpa only [ENNReal.toReal_one,Real.rpow_one,sourceH1WeightedActionSequence_apply,
    Complex.norm_real,Real.norm_of_nonneg (hn _)] using
    lp.norm_rpow_eq_tsum (by simp : 0 < (1:ℝ≥0∞).toReal) (sourceH1WeightedActionSequence a)

/-- The exact H1 action sequence supplies the angular-density mass majorant. -/
theorem sourceH1WeightedActionSequence_density_majorant (a : realTypeSobolevSourceLocus) (m : ℤ) :
    (∫ θ : ℝ, sourceGapAngularDensity (by simp) (by norm_num) (sourceH1RealSource a) m θ) ≤
      ‖sourceH1WeightedActionSequence a m‖/(1+|(m:ℝ)|)^2 := by
  have hn : 0 ≤ sourceWeightedActionTerm (sourceH1RealSource a) 1 m := by
    dsimp [sourceWeightedActionTerm]; positivity
  rw [integral_sourceGapAngularDensity,sourceH1WeightedActionSequence_apply,
    Complex.norm_real,Real.norm_of_nonneg hn,
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) m
      (sourceH1RealSource a).val (sourceH1RealSource a).property,sourceWeightedActionTerm]
  norm_num only [Nat.mul_one]
  have hw : (1+|(m:ℝ)|)^2 ≤ (1+|((2*m:ℤ):ℝ)*Real.pi|)^2 := by
    apply pow_le_pow_left₀ (by positivity)
    simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2),abs_of_pos Real.pi_pos]
    nlinarith [abs_nonneg (m:ℝ),Real.pi_gt_three]
  apply (le_div_iff₀ (by positivity)).mpr
  have h := mul_le_mul_of_nonneg_right hw
    (norm_nonneg (sourceRealAction (by simp) (by norm_num) (sourceH1RealSource a).val (sourceH1RealSource a).property m))
  nlinarith [mul_nonneg (sq_nonneg (1+|(m:ℝ)|))
    (norm_nonneg (sourceRealAction (by simp) (by norm_num) (sourceH1RealSource a).val (sourceH1RealSource a).property m))]

/-- The actual physical H1 action sequence is uniformly bounded on every physical H1 ball. -/
theorem exists_sourceH1WeightedActionSequence_bound_on_physical_ball (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ‖sourceH1WeightedActionSequence a‖ ≤ M := by
  obtain ⟨c,hc,hbound⟩ := exists_sourceWeightedAction_sobolev_upper_bound 1 le_rfl
  let w := SpectralWeight.piSobolev 1 (by norm_num)
  let L := normalizedWeightedSourceCLM (p := 2) w
  let M := c^2*(R^2+(1+R)^4*(‖L‖*R)^2)
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  intro a ha
  let b : realTypeHigherSobolevSourceLocus 1 := ⟨higherSobolevSourceOneEquiv a.val,by
    change IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion 1 (higherSobolevSourceOneEquiv a.val)))
    rw [higherSobolevSourceInclusion_one]
    exact a.property⟩
  have he : (⟨higherSobolevSourceInclusion 1 b.val,b.property⟩ : realTypeSourceSubmodule 2) = sourceH1RealSource a := by
    apply Subtype.ext
    exact higherSobolevSourceInclusion_one a.val
  have hreal : 0 ≤ R := (norm_nonneg _).trans ha
  have hL : ‖sobolevSourceInclusion a.val‖ ≤ ‖L‖*R := by
    have hh := L.le_opNorm (sourcePhysicalH1Coordinates a.val)
    change ‖normalizedWeightedSource w (sourcePhysicalH1Coordinates a.val)‖ ≤ _ at hh
    rw [normalizedWeightedSource_physicalH1Coordinates] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left ha (norm_nonneg L))
  have hb := hbound b
  rw [he] at hb
  rw [norm_sourceH1WeightedActionSequence]
  apply hb.trans
  change c^2*(‖sourcePhysicalH1Coordinates a.val‖^2+
    (1+‖sourcePhysicalH1Coordinates a.val‖)^(4*1)*‖higherSobolevSourceInclusion 1 b.val‖^2) ≤ M
  have hi : higherSobolevSourceInclusion 1 b.val = sobolevSourceInclusion a.val := higherSobolevSourceInclusion_one a.val
  rw [hi]
  dsimp only [M]
  norm_num only [Nat.mul_one]
  gcongr

end NLS.ZakharovShabat
