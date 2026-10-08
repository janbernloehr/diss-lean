import NLS.ZakharovShabat.M1SpectralLocalization
import NLS.ZakharovShabat.QuadraticCanonicalPeriodicPair
import NLS.ZakharovShabat.ResonantGapMajorant
import NLS.ZakharovShabat.DiscriminantPairFactorization

/-! # Canonical gap bounds for the full M₁ class

The linear bracket identifies the canonical labels and multiplicities.
The original weighted determinant then supplies the radius and gap estimates,
including the individual estimate (5.8), at the same explicit threshold.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- All M₁ weights have the canonical endpoint pair at the exact quadratic threshold. -/
theorem M1_canonicalEndpointPair (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    PeriodicEndpointPair (by simp) (weightedBaseToPair w φ) n
      (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven n)
      (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven n) := by
  have hpar : weightedBaseToPair (SpectralWeight.sobolev 1 (by norm_num)) (m1LinearInclusion w hw φ) ∈
      pairParitySubspace 0 := by simpa only [weightedBaseToPair_m1LinearInclusion] using heven
  have h := linearWeight_canonicalEndpointPair (SpectralWeight.sobolev 1 (by norm_num))
    (SpectralWeight.hasLinearFactor_sobolev 1 le_rfl) 1
    (by intro k; simp [Weight.sobolev_apply]) (m1LinearInclusion w hw φ) hpar n
    (m1LinearInclusion_threshold w hw φ n hn)
  simpa only [weightedBaseToPair_m1LinearInclusion] using h

/-- The actual canonically indexed M₁ endpoints obey the source radius and factor-six gap bound. -/
theorem M1_canonicalEndpoints_localization (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    ‖canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven n-(Real.pi:ℂ)*n‖ ≤
      quadraticLocalizationRadius ‖φ‖ n ∧
    ‖canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven n-(Real.pi:ℂ)*n‖ ≤
      quadraticLocalizationRadius ‖φ‖ n ∧
    ‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖^2 ≤
      6*resonantBProductSup (by simp) w φ n := by
  have hp := M1_canonicalEndpointPair w hw φ heven n hn
  have hs := canonicalPeriodicEndpoints_mem_spectrum (by simp) (by norm_num : (1:ENNReal) < 2)
    (weightedBaseToPair w φ) heven n
  have hx := refinedResonantDisk_subset_strip n hp.left_mem
  have hy := refinedResonantDisk_subset_strip n hp.right_mem
  have hdx := (mem_periodicSpectrum_iff_M1_determinant_zero w hw φ n hn _ hx).mp hs.1
  have hdy := (mem_periodicSpectrum_iff_M1_determinant_zero w hw φ n hn _ hy).mp hs.2
  exact ⟨(M1_periodicSpectrum_localization w hw φ n hn _ hx hs.1).1,
    (M1_periodicSpectrum_localization w hw φ n hn _ hy hs.2).1,
    linearWeight_determinant_root_gap_le w hw φ n hn _ _ hy hx hdy hdx⟩

/-- Equation (5.8), squared, with the exact doubled-frequency weight and Hilbert pair norm. -/
theorem M1_canonicalGap_weighted_sq_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2 ≤
      12*‖φ‖^2 := by
  have hg := mul_le_mul_of_nonneg_left (M1_canonicalEndpoints_localization w hw φ heven n hn).2.2
    (sq_nonneg (w (2*n)))
  have hb := weighted_resonantBProductSup_le (by simp) w φ n (2*‖φ.fst‖) (2*‖φ.snd‖)
    (by positivity) (fun z hz => (linearWeight_offDiagonal_le w hw φ n hn z hz).symm)
  rw [mul_pow,WithLp.prod_norm_sq_eq_of_L2]
  nlinarith [sq_nonneg (‖φ.fst‖-‖φ.snd‖)]

/-- The individual estimate (5.8) for arbitrary M₁ weights, including superlinear ones. -/
theorem M1_canonicalGap_weighted_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖ ≤
      Real.sqrt 12*‖φ‖ := by
  have h := M1_canonicalGap_weighted_sq_le w hw φ heven n hn
  have he : (Real.sqrt 12*‖φ‖)^2 = 12*‖φ‖^2 := by
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 12)]
  rw [← he] at h
  exact (sq_le_sq₀ (mul_nonneg (w.positive _).le (norm_nonneg _)) (by positivity)).mp h

end NLS.ZakharovShabat
