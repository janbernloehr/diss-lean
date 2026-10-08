import NLS.ZakharovShabat.LinearWeightResonantCoefficients

/-! # Lemma 25.3 on the full closed spectral strip

The explicit threshold places every strip point in the existing open analytic
correction domain. The total analytic extensions agree with the actual
resonant matrix coefficients and satisfy the source's uniform bounds.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The quadratic threshold puts the actual parameters in the analytic domain. -/
theorem mem_weightedCorrectionDomain_linear (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    (φ,z) ∈ weightedCorrectionDomain (by simp) w n :=
  mem_weightedCorrectionDomain (by simp) w φ n z hz
    ((norm_weightedPotentialSquareInShift_le_half w hw φ n z hz hn).trans_lt (by norm_num))

/-- Lemma 25.3: analyticity near every closed-strip point and all three uniform
bounds, with no additional qualitative frequency cutoff. -/
theorem linearWeight_resonantCoefficients (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    AnalyticOnNhd ℂ (weightedResonantAExtension (by simp) w φ n) (resonantStrip n) ∧
    AnalyticOnNhd ℂ (weightedResonantBPlusExtension (by simp) w φ n) (resonantStrip n) ∧
    AnalyticOnNhd ℂ (weightedResonantBMinusExtension (by simp) w φ n) (resonantStrip n) ∧
    ∀ z ∈ resonantStrip n,
      ‖weightedResonantAExtension (by simp) w φ n z‖ ≤ ‖φ‖^2/(1+|(n:ℝ)|) ∧
      w (2*n)*‖weightedResonantBPlusExtension (by simp) w φ n z-φ.snd.val (2*n)‖ ≤
        (8/(1+|(n:ℝ)|))*‖φ‖^2*‖φ.snd‖ ∧
      w (2*n)*‖weightedResonantBMinusExtension (by simp) w φ n z-φ.fst.val (-(2*n))‖ ≤
        (8/(1+|(n:ℝ)|))*‖φ‖^2*‖φ.fst‖ := by
  have hdom (z : ℂ) (hz : z ∈ resonantStrip n) := mem_weightedCorrectionDomain_linear w hw φ n z hz hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (analyticAt_weightedResonantAExtension (by simp) w n (φ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  · intro z hz
    exact (analyticAt_weightedResonantBPlusExtension (by simp) w n (φ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  · intro z hz
    exact (analyticAt_weightedResonantBMinusExtension (by simp) w n (φ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  · intro z hz
    have h := (norm_weightedPotentialSquareInShift_le_half w hw φ n z hz hn).trans_lt (by norm_num : (1/2:ℝ) < 1)
    rw [weightedResonantAExtension_eq (by simp) w φ n z hz h,
      weightedResonantBPlusExtension_eq (by simp) w φ n z hz h,
      weightedResonantBMinusExtension_eq (by simp) w φ n z hz h]
    exact ⟨norm_weightedResonantA_linear w hw φ n z hz h hn,
      weightedResonantBPlus_remainder_linear w hw φ n z hz h hn,
      weightedResonantBMinus_remainder_linear w hw φ n z hz h hn⟩

end NLS.ZakharovShabat
