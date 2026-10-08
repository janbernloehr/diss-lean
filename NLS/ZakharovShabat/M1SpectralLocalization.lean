import NLS.ZakharovShabat.DominatedWeightCorrection
import NLS.ZakharovShabat.LinearWeightSpectralLocalization

/-! # Exact-threshold spectral localization for every M₁ weight

Comparison with the linear bracket removes the linear upper-growth
assumption. Both corrections contract at the same quantitative threshold.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every M₁ potential has a norm-decreasing realization at the linear bracket weight. -/
def m1LinearInclusion (w : SpectralWeight) (hw : w.HasLinearFactor) :
    WeightedCoeffPair w.toWeight 2 →L[ℂ]
      WeightedCoeffPair (SpectralWeight.sobolev 1 (by norm_num)).toWeight 2 :=
  w.inclusionPair (SpectralWeight.sobolev 1 (by norm_num))
    (fun k => by simpa [Weight.sobolev_apply] using SpectralWeight.bracket_le_of_hasLinearFactor hw k)

@[simp] theorem weightedBaseToPair_m1LinearInclusion (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) :
    weightedBaseToPair (SpectralWeight.sobolev 1 (by norm_num)) (m1LinearInclusion w hw φ) =
      weightedBaseToPair w φ := weightedBaseToPair_inclusionPair w _ _ φ

theorem norm_m1LinearInclusion_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) : ‖m1LinearInclusion w hw φ‖ ≤ ‖φ‖ :=
  SpectralWeight.norm_inclusionPair_le (by simp) w _ _ φ

/-- Lowering to the bracket weight preserves the exact threshold. -/
theorem m1LinearInclusion_threshold (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    8*‖m1LinearInclusion w hw φ‖^2 ≤ 1+|(n:ℝ)| := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_m1LinearInclusion_le w hw φ) 2
  linarith

/-- The original spectrum and weighted determinant agree at the quadratic threshold for all M₁ weights. -/
theorem mem_periodicSpectrum_iff_M1_determinant_zero (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    z ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ) ↔
      resonantDeterminantExtension (by simp) w φ n z = 0 := by
  let v := SpectralWeight.sobolev 1 (by norm_num)
  have hv : v.HasLinearFactor := SpectralWeight.hasLinearFactor_sobolev 1 le_rfl
  have ht := m1LinearInclusion_threshold w hw φ n hn
  have he := resonantDeterminantExtension_inclusion (by simp) w v
    (fun k => by simpa [v,Weight.sobolev_apply] using SpectralWeight.bracket_le_of_hasLinearFactor hw k)
    φ n z hz
    ((norm_weightedPotentialSquareInShift_le_half w hw φ n z hz hn).trans_lt (by norm_num))
    ((norm_weightedPotentialSquareInShift_le_half v hv (m1LinearInclusion w hw φ) n z hz ht).trans_lt (by norm_num))
  rw [he]
  simpa only [v,m1LinearInclusion,weightedBaseToPair_inclusionPair] using
    mem_periodicSpectrum_iff_linearWeight_determinant_zero v hv 1
      (by intro k; simp [v,Weight.sobolev_apply]) (m1LinearInclusion w hw φ) n ht z hz

/-- The source radius localizes every original strip eigenvalue for the full M₁ class. -/
theorem M1_periodicSpectrum_localization (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n)
    (hs : z ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ)) :
    ‖z-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧ z ∈ refinedResonantDisk n :=
  linearWeight_determinant_root_localization w hw φ n hn z hz
    ((mem_periodicSpectrum_iff_M1_determinant_zero w hw φ n hn z hz).mp hs)

end NLS.ZakharovShabat
