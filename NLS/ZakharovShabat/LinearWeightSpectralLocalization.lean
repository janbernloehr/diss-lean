import NLS.ZakharovShabat.SobolevWeightedSpectralBridge
import NLS.ZakharovShabat.LinearWeightRoots

/-! # Quantitative localization of the original periodic spectrum

Regularity identifies weighted determinant zeros with original spectral
points at the explicit quadratic threshold. The source H¹ weight is included.
Canonical signed labels and algebraic spectral multiplicities are separate.
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- At the quadratic threshold a linearly growing M₁ weight needs no unit-weight contraction. -/
theorem mem_periodicSpectrum_iff_linearWeight_determinant_zero (w : SpectralWeight)
    (hw : w.HasLinearFactor) (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    z ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ) ↔
      resonantDeterminantExtension (by simp) w φ n z = 0 := by
  rw [mem_periodicSpectrum_iff_linearWeight_eigenvector (by simp) w
    (SpectralWeight.bracket_le_of_hasLinearFactor hw) C hu]
  exact weighted_eigenvector_iff_resonantDeterminantExtension_zero (by simp) w φ n z hz
    ((norm_weightedPotentialSquareInShift_le_half w hw φ n z hz hn).trans_lt (by norm_num))

/-- Every original spectral point in the strip satisfies the explicit source radius. -/
theorem linearWeight_periodicSpectrum_localization (w : SpectralWeight)
    (hw : w.HasLinearFactor) (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (z : ℂ) (hz : z ∈ resonantStrip n)
    (hs : z ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ)) :
    ‖z-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧ z ∈ refinedResonantDisk n :=
  linearWeight_determinant_root_localization w hw φ n hn z hz
    ((mem_periodicSpectrum_iff_linearWeight_determinant_zero w hw C hu φ n hn z hz).mp hs)

/-- The original strip spectrum is exhausted by the two determinant roots, with possible repetition. -/
theorem linearWeight_exists_periodicRoots (w : SpectralWeight)
    (hw : w.HasLinearFactor) (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    ∃ x ∈ refinedResonantDisk n, ∃ y ∈ refinedResonantDisk n,
      x ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ) ∧
      y ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ) ∧
      (∀ z ∈ resonantStrip n,
        z ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ) ↔ z = x ∨ z = y) ∧
      (∀ z ∈ resonantStrip n,
        analyticOrderNatAt (resonantDeterminantExtension (by simp) w φ n) z =
          ({x,y} : Multiset ℂ).count z) ∧
      ‖x-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧
      ‖y-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧
      ‖x-y‖^2 ≤ 6*resonantBProductSup (by simp) w φ n := by
  obtain ⟨x,hx,y,hy,hxz,hyz,he,hm,hxl,hyl,hgap⟩ := linearWeight_exists_resonantRoots w hw φ n hn
  have hs := mem_periodicSpectrum_iff_linearWeight_determinant_zero w hw C hu φ n hn
  exact ⟨x,hx,y,hy,(hs x (refinedResonantDisk_subset_strip n hx)).mpr hxz,
    (hs y (refinedResonantDisk_subset_strip n hy)).mpr hyz,
    fun z hz => (hs z hz).trans (he z hz),hm,hxl,hyl,hgap⟩

/-- The factor-six gap estimate applies directly to original spectral points. -/
theorem linearWeight_periodicSpectrum_gap_le (w : SpectralWeight)
    (hw : w.HasLinearFactor) (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (x y : ℂ) (hx : x ∈ resonantStrip n) (hy : y ∈ resonantStrip n)
    (hsx : x ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ))
    (hsy : y ∈ periodicSpectrum (by simp) (weightedBaseToPair w φ)) :
    ‖x-y‖^2 ≤ 6*resonantBProductSup (by simp) w φ n :=
  linearWeight_determinant_root_gap_le w hw φ n hn x y hx hy
    ((mem_periodicSpectrum_iff_linearWeight_determinant_zero w hw C hu φ n hn x hx).mp hsx)
    ((mem_periodicSpectrum_iff_linearWeight_determinant_zero w hw C hu φ n hn y hy).mp hsy)

/-- The exact source H¹ weight has a linear upper bound with constant π. -/
theorem piSobolev_one_le_pi_bracket (k : ℤ) :
    SpectralWeight.piSobolev 1 (by norm_num) k ≤ Real.pi*(1+|(k:ℝ)|) := by
  simp only [SpectralWeight.piSobolev_apply, Real.rpow_one, abs_mul, abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_gt_three]

/-- Lemma 25.4's equivalence with the original spectrum for the exact H¹ norm. -/
theorem mem_periodicSpectrum_iff_H1_determinant_zero
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) (z : ℂ) (hz : z ∈ resonantStrip n) :
    z ∈ periodicSpectrum (by simp) (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) ↔
      resonantDeterminantExtension (by simp) (SpectralWeight.piSobolev 1 (by norm_num)) φ n z = 0 :=
  mem_periodicSpectrum_iff_linearWeight_determinant_zero _
    (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl) Real.pi piSobolev_one_le_pi_bracket φ n hn z hz

/-- Original H¹ spectral points lie in the stated radius, at the stated threshold. -/
theorem H1_periodicSpectrum_localization
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hs : z ∈ periodicSpectrum (by simp) (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ)) :
    ‖z-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧ z ∈ refinedResonantDisk n :=
  linearWeight_periodicSpectrum_localization _ (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl)
    Real.pi piSobolev_one_le_pi_bracket φ n hn z hz hs

end NLS.ZakharovShabat
