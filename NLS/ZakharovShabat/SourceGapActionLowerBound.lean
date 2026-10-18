import NLS.ZakharovShabat.SourcePrimitivePowerGlobalCubic

/-! # The sharp actual gap-action lower bound

The positive finite-gap profile dominates the semicircle profile. Integration
gives gamma_n squared <= 4 I_n; continuity and finite-gap density extend it
to every real source at every finite exponent p > 1. Collapsed gaps are
included and the final theorem constructs its primitive atlas internally.
-/

noncomputable section
open Set Metric Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)
include A

/-- A positive correction of the semicircle profile gives the sharp gap-action lower bound. -/
theorem real_gap_sq_le_four_action_of_profile_correction
    (φ : realTypeSourceSubmodule p) (n : ℤ) (V : ℝ → ℝ)
    (hV : Continuous V) (hn : ∀ x ∈ Icc (0:ℝ) Real.pi, 0 ≤ V x)
    (hrep : ∀ x ∈ Icc (0:ℝ) Real.pi,
      sourceRealGapCosineProfile hp hp1 φ.val n x =
        (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re/2*
          Real.sin x*(1+V x)) :
    (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re^2 ≤
      4*‖sourceComplexAction hp hp1 n φ.val‖ := by
  let g := (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
  let f := sourceRealGapCosineProfile hp hp1 φ.val n
  change ∀ x ∈ Icc (0:ℝ) Real.pi, f x = g/2*Real.sin x*(1+V x) at hrep
  have hg : 0 ≤ g := by
    have h := NLS.ComplexAnalysis.re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val)).2.1 n)
    simpa only [g,canonicalPeriodicGap,Complex.sub_re,sub_nonneg] using h
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
  have i2 : IntervalIntegrable (fun x : ℝ => (Real.sin x)^2) volume 0 Real.pi :=
    (Real.continuous_sin.pow 2).intervalIntegrable _ _
  have iv : IntervalIntegrable (fun x : ℝ => (Real.sin x)^2*V x) volume 0 Real.pi :=
    ((Real.continuous_sin.pow 2).mul hV).intervalIntegrable _ _
  have hint : (∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*(1+V x)) =
      Real.pi/2 + (∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*V x) := by
    simp_rw [mul_add,mul_one]
    rw [intervalIntegral.integral_add i2 iv]
    simp [integral_sin_sq]
  have hpos : 0 ≤ ∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*V x :=
    intervalIntegral.integral_nonneg Real.pi_pos.le (fun x hx => mul_nonneg (sq_nonneg _) (hn x hx))
  rw [hfirst,ha,hint]
  change g^2 ≤ _
  have h := mul_nonneg (div_nonneg hg Real.pi_pos.le) (mul_nonneg (div_nonneg hg (by positivity)) hpos)
  field_simp at h ⊢
  nlinarith

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas

namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)
include A

/-- The exact finite-gap profile proves the sharp action lower bound. -/
theorem real_gap_sq_le_four_action_finiteGap
    (φ : realTypeSourceSubmodule p) (n : ℤ) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re^2 ≤
      4*‖sourceComplexAction hp hp1 n φ.val‖ := by
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · simp only [hg,Complex.zero_re,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    positivity
  obtain ⟨V,_,_,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hcenter⟩ := hC φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  apply A.real_gap_sq_le_four_action_of_profile_correction φ n (sourceExteriorGapCorrection hp hp1 φ n)
    (continuous_sourceExteriorGapCorrection hp hp1 φ n hg (A.summable_actions_of_finiteGap φ hf))
    (fun x _ => sourceExteriorGapCorrection_nonneg hp hp1 φ n hg x)
  simpa only [sourceGapHalfWidthReal,canonicalPeriodicGap,Complex.sub_re] using
    C.real_profile_eq_actual_correction_finiteGap n φ hφ hf hg

/-- Density gives the sharp gap-action bound on every real source at every finite p>1. -/
theorem real_gap_sq_le_four_action (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re^2 ≤
      4*‖sourceComplexAction hp hp1 n φ.val‖ := by
  have hg : Continuous (fun ψ : realTypeSourceSubmodule p =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n).re) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    have hL := continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 ψ.val ψ.property n
    have hR := continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 ψ.val ψ.property n
    simpa only [canonicalPeriodicGap, Function.comp_def, Pi.sub_apply] using!
      Complex.continuous_re.continuousAt.comp ((hR.sub hL).comp continuous_subtype_val.continuousAt)
  have hc : IsClosed {ψ : realTypeSourceSubmodule p |
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n).re^2 ≤
        4*‖A.moment n 1 ψ.val‖} :=
    isClosed_le (hg.pow 2) (continuous_const.mul (A.continuous_real_moment n 1).norm)
  have hsub : sourceFiniteGapLocus hp hp1 ⊆ {ψ : realTypeSourceSubmodule p |
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n).re^2 ≤
        4*‖A.moment n 1 ψ.val‖} := by
    intro ψ hψ
    change _ ≤ 4*‖A.moment n 1 ψ.val‖
    rw [A.moment_one n (A.realType_subset_domain ψ.property)]
    exact A.real_gap_sq_le_four_action_finiteGap ψ n hψ
  have h := closure_minimal hsub hc (dense_sourceFiniteGapLocus hp hp1 φ)
  change _ ≤ 4*‖A.moment n 1 φ.val‖ at h
  rwa [A.moment_one n (A.realType_subset_domain φ.property)] at h

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The sharp gap-action estimate for the actual canonical quantities, with no supplied atlas. -/
theorem source_gap_norm_sq_le_four_action (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    ‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖^2 ≤
      4*‖sourceComplexAction hp hp1 n φ.val‖ := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas hp hp1
  have hi := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _ (periodOnePotential_mem φ.val)
    (isRealType_periodOnePotential φ.val φ.property) n
  have he : ‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖^2 =
      (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re^2 := by
    rw [Complex.sq_norm]
    simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,
      Complex.normSq_apply,Complex.sub_re,Complex.sub_im,hi.1,hi.2,sub_self,mul_zero,add_zero,pow_two]
  rw [he]
  exact A.real_gap_sq_le_four_action φ n

end NLS.ZakharovShabat