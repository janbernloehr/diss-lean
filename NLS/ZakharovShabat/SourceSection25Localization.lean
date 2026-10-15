import NLS.ZakharovShabat.QuadraticSpectralBox
import NLS.ZakharovShabat.QuadraticCanonicalPeriodicPair
import NLS.ZakharovShabat.SourcePiSobolevCoordinates

/-! # Original Section 25 spectral localization

The source norm is the literal Hilbert norm weighted by 1+|2nπ|.
Canonical signed endpoints and their algebraic multiplicities are retained.
No extra qualitative cutoff or real-type premise is imposed.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Theorem 25.1 on every original complex H¹ source, with the exact physical norm. -/
theorem sourceH1_uniform_localization (a : SobolevSource 1) :
    let ψ := higherSobolevSourceInclusion 1 a
    let P := ‖sourcePiSobolevCoordinates 1 1 le_rfl a‖
    (∀ n : ℤ, 8*P^2 ≤ 1+|(n:ℝ)| →
      ‖canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n
        -(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius P n ∧
      ‖canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n
        -(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius P n ∧
      quadraticLocalizationRadius P n < Real.pi/5) ∧
    (∀ n : ℤ, 1+|(n:ℝ)| < 8*P^2 →
      canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n
        ∈ quadraticSpectralBox P ∧
      canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n
        ∈ quadraticSpectralBox P) := by
  let w := SpectralWeight.piSobolev 1 (by norm_num)
  let φ := normalizedWeightedPeriodOne w (sourcePiSobolevCoordinates 1 1 le_rfl a)
  have he : weightedBaseToPair w φ = periodOnePotential (higherSobolevSourceInclusion 1 a) :=
    weightedBaseToPair_sourcePiSobolevOne 1 le_rfl a
  have heven : weightedBaseToPair w φ ∈ pairParitySubspace 0 := he ▸ periodOnePotential_mem _
  have h := H1_periodicSpectrum_uniform_localization φ heven
  simpa only [φ,w,weightedBaseToPair_sourcePiSobolevOne,norm_normalizedWeightedPeriodOne] using h

/-- The entire original periodic spectrum lies in the printed box or the explicit distant discs. -/
theorem sourceH1_spectrum_subset (a : SobolevSource 1) (z : ℂ)
    (hz : z ∈ periodicSpectrum (by simp) (periodOnePotential (higherSobolevSourceInclusion 1 a))) :
    z ∈ quadraticSpectralBox ‖sourcePiSobolevCoordinates 1 1 le_rfl a‖ ∨
      ∃ n : ℤ, 8*‖sourcePiSobolevCoordinates 1 1 le_rfl a‖^2 ≤ 1+|(n:ℝ)| ∧
        ‖z-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖sourcePiSobolevCoordinates 1 1 le_rfl a‖ n := by
  let w := SpectralWeight.piSobolev 1 (by norm_num)
  let φ := normalizedWeightedPeriodOne w (sourcePiSobolevCoordinates 1 1 le_rfl a)
  have he : weightedBaseToPair w φ = periodOnePotential (higherSobolevSourceInclusion 1 a) :=
    weightedBaseToPair_sourcePiSobolevOne 1 le_rfl a
  have heven : weightedBaseToPair w φ ∈ pairParitySubspace 0 := he ▸ periodOnePotential_mem _
  simpa only [φ,norm_normalizedWeightedPeriodOne] using
    H1_periodicSpectrum_subset_box_union_discs φ heven z (by simpa only [φ,w,weightedBaseToPair_sourcePiSobolevOne] using hz)

/-- Lemma 25.4 with the actual canonical pair, exact multiplicities, and factor-six gap bound. -/
theorem sourceH1_canonical_pair (a : SobolevSource 1)
    (n : ℤ) (hn : 8*‖sourcePiSobolevCoordinates 1 1 le_rfl a‖^2 ≤ 1+|(n:ℝ)|) :
    let ψ := higherSobolevSourceInclusion 1 a
    let w := SpectralWeight.piSobolev 1 (by norm_num)
    let φ := normalizedWeightedPeriodOne w (sourcePiSobolevCoordinates 1 1 le_rfl a)
    let x := canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    let y := canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    PeriodicEndpointPair (by simp) (periodOnePotential ψ) n x y ∧
    (∀ z ∈ resonantStrip n, resonantDeterminantExtension (by simp) w φ n z = 0 ↔ z = x ∨ z = y) ∧
    (∀ z ∈ resonantStrip n, analyticOrderNatAt (resonantDeterminantExtension (by simp) w φ n) z =
      ({x,y} : Multiset ℂ).count z) ∧
    ‖y-x‖^2 ≤ 6*resonantBProductSup (by simp) w φ n := by
  let w := SpectralWeight.piSobolev 1 (by norm_num)
  let φ := normalizedWeightedPeriodOne w (sourcePiSobolevCoordinates 1 1 le_rfl a)
  have he : weightedBaseToPair w φ = periodOnePotential (higherSobolevSourceInclusion 1 a) :=
    weightedBaseToPair_sourcePiSobolevOne 1 le_rfl a
  have heven : weightedBaseToPair w φ ∈ pairParitySubspace 0 := he ▸ periodOnePotential_mem _
  have h := H1_canonical_periodic_localization φ heven n
    (by simpa only [φ,norm_normalizedWeightedPeriodOne] using hn)
  dsimp only at h
  have h' := And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2.2.2.2))
  simpa only [φ,w,weightedBaseToPair_sourcePiSobolevOne] using h'

end NLS.ZakharovShabat
