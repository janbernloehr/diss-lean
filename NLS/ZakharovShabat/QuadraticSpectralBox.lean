import NLS.ZakharovShabat.H1SpectralHeight
import NLS.ZakharovShabat.QuadraticCentralStrip

/-! # Theorem 25.1: uniform H¹ localization of the periodic spectrum

Canonical endpoints above the exact quadratic threshold lie in the source
discs; every remaining indexed endpoint lies in the printed central box.
The imaginary bound holds globally and needs no parity assumption.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- The central box printed in Theorem 25.1, with the exact source H¹ norm. -/
def quadraticSpectralBox (P : ℝ) : Set ℂ :=
  {z | |z.re| ≤ (8*P^2-1/2)*Real.pi ∧ |z.im| ≤ P}

/-- Both canonically indexed eigenvalues below the quadratic threshold lie in the central box. -/
theorem H1_canonicalEndpoints_mem_centralBox
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 1+|(n:ℝ)| < 8*‖φ‖^2) :
    canonicalPeriodicLeft (by simp) (by norm_num)
      (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) heven n ∈ quadraticSpectralBox ‖φ‖ ∧
    canonicalPeriodicRight (by simp) (by norm_num)
      (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) heven n ∈ quadraticSpectralBox ‖φ‖ := by
  have hr := linearWeight_canonicalEndpoints_central_re _
    (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl) Real.pi piSobolev_one_le_pi_bracket φ heven n hn
  have hs := canonicalPeriodicEndpoints_mem_spectrum (by simp) (by norm_num : (1:ENNReal) < 2)
    (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) heven n
  exact ⟨⟨hr.1.le,abs_im_le_H1_norm φ _ hs.1⟩,⟨hr.2.le,abs_im_le_H1_norm φ _ hs.2⟩⟩

/-- Theorem 25.1 with canonical signed endpoints and the exact threshold and box constants. -/
theorem H1_periodicSpectrum_uniform_localization
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0) :
    let w := SpectralWeight.piSobolev 1 (by norm_num)
    let ξ := canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven
    let η := canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven
    (∀ n : ℤ, 8*‖φ‖^2 ≤ 1+|(n:ℝ)| →
      ‖ξ n-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧
      ‖η n-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧
      quadraticLocalizationRadius ‖φ‖ n < Real.pi/5) ∧
    (∀ n : ℤ, 1+|(n:ℝ)| < 8*‖φ‖^2 →
      ξ n ∈ quadraticSpectralBox ‖φ‖ ∧ η n ∈ quadraticSpectralBox ‖φ‖) := by
  refine ⟨?_,H1_canonicalEndpoints_mem_centralBox φ heven⟩
  intro n hn
  have h := H1_canonical_periodic_localization φ heven n hn
  exact ⟨h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1⟩

/-- The whole original spectrum lies in the central box or a quantitative source disc. -/
theorem H1_periodicSpectrum_subset_box_union_discs
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0)
    (z : ℂ) (hz : z ∈ periodicSpectrum (by simp)
      (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ)) :
    z ∈ quadraticSpectralBox ‖φ‖ ∨ ∃ n : ℤ, 8*‖φ‖^2 ≤ 1+|(n:ℝ)| ∧
      ‖z-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n := by
  obtain ⟨n,hn⟩ := (canonicalPeriodicEndpoints_exhaustive (by simp) (by norm_num : (1:ENNReal) < 2)
    (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) heven z).mp hz
  have h := H1_periodicSpectrum_uniform_localization φ heven
  by_cases ht : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|
  · right
    refine ⟨n,ht,?_⟩
    rcases hn with rfl | rfl
    · exact (h.1 n ht).1
    · exact (h.1 n ht).2.1
  · left
    rcases hn with rfl | rfl
    · exact (h.2 n (lt_of_not_ge ht)).1
    · exact (h.2 n (lt_of_not_ge ht)).2

end NLS.ZakharovShabat
