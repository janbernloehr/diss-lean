import NLS.ZakharovShabat.SourceM1GapFactorBound
import NLS.ZakharovShabat.SourceNormalizedActionComplexExtension
import NLS.ZakharovShabat.NormalizedWeightedSourceRealPart

/-! # Bounds on the removable normalized action, including collapsed real gaps -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a collapsed gap, four times the normalized action equals the midpoint factor. -/
theorem sourceNormalizedAction_four_eq_gapFactor_of_collapsed (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0) :
    4*sourceNormalizedActionComplexExtension hp hp1 n ψ =
      sourceRealGapFactor hp hp1 ψ hreal n ⟨0,by norm_num⟩ := by
  simp only [sourceNormalizedActionComplexExtension,sourceNormalizedActionRealExtension,
    if_pos hgap,sourceNormalizedActionCollapsedCandidate]
  change 4*(I*sourceCriticalRootRatioExtension hp hp1 n ψ
    (sourceStandardRootMidpoint hp hp1 ψ n)/4) =
    I*sourceCriticalRootRatioExtension hp hp1 n ψ
      (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(0:ℂ))
  simp only [mul_zero,add_zero]
  ring

/-- The real gap-factor estimate controls the removable quotient even when the gap vanishes. -/
theorem sourceNormalizedAction_le_three_gapFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    ‖4*sourceNormalizedActionComplexExtension hp hp1 n ψ‖ ≤
      3*‖sourceRealGapFactor hp hp1 ψ hreal n‖ := by
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · rw [sourceNormalizedAction_four_eq_gapFactor_of_collapsed hp hp1 ψ hreal n hgap]
    have h := (sourceRealGapFactor hp hp1 ψ hreal n).norm_coe_le_norm ⟨0,by norm_num⟩
    nlinarith [norm_nonneg (sourceRealGapFactor hp hp1 ψ hreal n)]
  · simpa only [sourceNormalizedActionComplexExtension,sourceNormalizedActionRealExtension,
      if_neg hgap] using sourceRawNormalizedAction_le_three_gapFactor hp hp1 ψ hreal n hgap

/-- Every M₁ weight gives the real normalized-action bound with the inclusive cutoff margin. -/
theorem sourceM1_real_normalizedAction_le_1536 (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : realTypeSourceSubmodule 2) (n : ℤ) (hn : 8*‖a.val‖^2 ≤ 1+|(n:ℝ)|) :
    ‖sourceNormalizedActionComplexExtension (by simp) (by norm_num) n
      (normalizedWeightedSource w a.val)‖ ≤ 1536*(1+‖a.val‖^2) := by
  let ψ : realTypeSourceSubmodule 2 :=
    ⟨normalizedWeightedSource w a.val,normalizedWeightedSource_realType w a.val a.property⟩
  let φ := normalizedWeightedPeriodOne w a.val
  let K : ℕ := ⌊8*‖a.val‖^2⌋₊
  let N := min n.natAbs K
  have hfloor : (K:ℝ) ≤ 8*‖a.val‖^2 := Nat.floor_le (by positivity)
  have hK : 8*‖a.val‖^2 ≤ 1+(K:ℝ) := by
    have h := Nat.lt_floor_add_one (8*‖a.val‖^2)
    dsimp [K]
    linarith
  have hN : 8*‖a.val‖^2 ≤ 1+(N:ℝ) := by
    by_cases h : n.natAbs ≤ K
    · simpa only [N,min_eq_left h,Nat.cast_natAbs,Int.cast_abs] using hn
    · simpa only [N,min_eq_right (le_of_not_ge h)] using hK
  have hcut : (N:ℝ) ≤ 8*‖a.val‖^2 :=
    (show (N:ℝ) ≤ (K:ℝ) by exact_mod_cast min_le_right n.natAbs K).trans hfloor
  have hb := sourceM1_real_gapFactor_le_2048_at_cutoff w hw ψ φ
    (weightedBaseToPair_normalizedWeightedPeriodOne w a.val) N
    (by simpa only [φ,norm_normalizedWeightedPeriodOne] using hN)
    (by simpa only [φ,norm_normalizedWeightedPeriodOne] using hcut) n (min_le_left _ _)
  simp only [φ,norm_normalizedWeightedPeriodOne] at hb
  have h := sourceNormalizedAction_le_three_gapFactor (by simp) (by norm_num) ψ.val ψ.property n
  simp only [norm_mul,Complex.norm_ofNat] at h
  change ‖sourceNormalizedActionComplexExtension (by simp) (by norm_num) n ψ.val‖ ≤ _
  linarith

end NLS.ZakharovShabat
