import NLS.ZakharovShabat.LinearWeightSandwich
import NLS.ZakharovShabat.WeightedSquareEstimate

/-! # Lemma 25.2 and its explicit quadratic contraction threshold

For every weight in M₁ the actual squared potential inverse obeys the
4‖φ‖²/⟨n⟩ estimate in the shifted Hilbert pair norm. Consequently the square
is a half-contraction once ⟨n⟩ ≥ 8‖φ‖², uniformly on the full closed strip.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Lemma 25.2 for the actual operator, in the dissertation's shifted pair norm. -/
theorem shiftedPairNorm_weightedPotentialInverse_sq_linear (w : SpectralWeight)
    (hw : w.HasLinearFactor) (φ : WeightedCoeffPair w.toWeight 2)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight 2) :
    w.shiftedPairNorm n (weightedPotentialInverse (by simp) w φ n z hz
      (weightedPotentialInverse (by simp) w φ n z hz f)) ≤
      (4/(1+|(n:ℝ)|))*‖φ‖^2*w.shiftedPairNorm n f := by
  let T := weightedPotentialInverse (by simp) w φ n z hz
  let C := (4/(1+|(n:ℝ)|))*‖φ‖^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hφ₁ : ‖φ.fst‖ ≤ ‖φ‖ := WithLp.norm_fst_le _ φ
  have hφ₂ : ‖φ.snd‖ ≤ ‖φ‖ := WithLp.norm_snd_le _ φ
  have h₁ : w.shiftedNorm (-n) (T (T f)).fst ≤ C*w.shiftedNorm (-n) f.fst := by
    rw [weightedPotentialInverse_sq_fst]
    have hi := shiftedNorm_complementarySandwich_false_linear w hw φ.snd f.fst hz
    have hf0 : 0 ≤ w.shiftedNorm (-n) f.fst := norm_nonneg _
    calc
      _ ≤ ‖φ.fst‖*w.shiftedNorm (-n) (complementarySandwich (by simp) w φ.snd n z hz false f.fst) :=
        w.shiftedNorm_convolution_le _ _ _
      _ ≤ ‖φ.fst‖*((4/(1+|(n:ℝ)|))*‖φ.snd‖*w.shiftedNorm (-n) f.fst) :=
        mul_le_mul_of_nonneg_left hi (norm_nonneg _)
      _ ≤ ‖φ‖*((4/(1+|(n:ℝ)|))*‖φ‖*w.shiftedNorm (-n) f.fst) := by gcongr
      _ = _ := by dsimp [C]; ring
  have h₂ : w.shiftedNorm n (T (T f)).snd ≤ C*w.shiftedNorm n f.snd := by
    rw [weightedPotentialInverse_sq_snd]
    have hi := shiftedNorm_complementarySandwich_linear w hw φ.fst f.snd hz true
    simp only [reciprocalCenter, freeFrequency_true, neg_neg] at hi
    have hf0 : 0 ≤ w.shiftedNorm n f.snd := norm_nonneg _
    calc
      _ ≤ ‖φ.snd‖*w.shiftedNorm n (complementarySandwich (by simp) w φ.fst n z hz true f.snd) :=
        w.shiftedNorm_convolution_le _ _ _
      _ ≤ ‖φ.snd‖*((4/(1+|(n:ℝ)|))*‖φ.fst‖*w.shiftedNorm n f.snd) :=
        mul_le_mul_of_nonneg_left hi (norm_nonneg _)
      _ ≤ ‖φ‖*((4/(1+|(n:ℝ)|))*‖φ‖*w.shiftedNorm n f.snd) := by gcongr
      _ = _ := by dsimp [C]; ring
  change ‖w.pairModulation n (T (T f))‖ ≤ C*‖w.pairModulation n f‖
  calc
    _ ≤ ‖(C:ℂ) • w.pairModulation n f‖ := by
      apply WeightedCoeffPair.norm_mono (by simp : (2:ℝ≥0∞) ≠ ⊤)
      · change ‖w.modulation (-n) (T (T f)).fst‖ ≤ ‖(C:ℂ) • w.modulation (-n) f.fst‖
        simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC,
          SpectralWeight.norm_modulation] using h₁
      · change ‖w.modulation n (T (T f)).snd‖ ≤ ‖(C:ℂ) • w.modulation n f.snd‖
        simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC,
          SpectralWeight.norm_modulation] using h₂
    _ = _ := by simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

/-- The exact norm estimate for the square conjugated by the source shift. -/
theorem norm_weightedPotentialSquareInShift_linear (w : SpectralWeight)
    (hw : w.HasLinearFactor) (φ : WeightedCoeffPair w.toWeight 2)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    ‖weightedPotentialSquareInShift (by simp) w φ n z hz‖ ≤ (4/(1+|(n:ℝ)|))*‖φ‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (show 0 ≤ (4/(1+|(n:ℝ)|))*‖φ‖^2 by positivity)
  intro f
  have h := shiftedPairNorm_weightedPotentialInverse_sq_linear w hw φ n z hz ((w.pairModulation n).symm f)
  simpa only [weightedPotentialSquareInShift, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, SpectralWeight.shiftedPairNorm,
    ContinuousLinearEquiv.apply_symm_apply] using h

/-- The explicit quadratic threshold immediately following Lemma 25.2. -/
theorem norm_weightedPotentialSquareInShift_le_half (w : SpectralWeight)
    (hw : w.HasLinearFactor) (φ : WeightedCoeffPair w.toWeight 2)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    ‖weightedPotentialSquareInShift (by simp) w φ n z hz‖ ≤ (1/2:ℝ) := by
  apply (norm_weightedPotentialSquareInShift_linear w hw φ n z hz).trans
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

end NLS.ZakharovShabat
