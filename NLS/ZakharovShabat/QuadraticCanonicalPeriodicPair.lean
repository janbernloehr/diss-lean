import NLS.ZakharovShabat.LinearWeightCanonicalLocalization
import NLS.ZakharovShabat.EndpointPairOfStripCount

/-! # Lemma 25.4 with canonical signed labels

The two determinant roots coincide, with multiplicity, with the canonical
periodic endpoints at the explicit quadratic threshold. The source radius
and factor-six gap bound use the exact π-normalized H¹ norm.
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- Canonical signed endpoints exhaust the quantitative strip with original multiplicities. -/
theorem linearWeight_canonicalEndpointPair (w : SpectralWeight) (hw : w.HasLinearFactor)
    (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|)) (φ : WeightedCoeffPair w.toWeight 2)
    (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    PeriodicEndpointPair (by simp) (weightedBaseToPair w φ) n
      (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven n)
      (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven n) := by
  obtain ⟨N₀,_,U,_,_,hφ,_,hlabels⟩ := exists_uniform_canonicalPeriodicEndpoints
    (by simp) (by norm_num : (1:ENNReal) < 2) w φ
  let N := max N₀ n.natAbs
  have hl := hlabels φ hφ heven N (le_max_left _ _)
  have hnN : n.natAbs ≤ N := le_max_right _ _
  have hc := linearWeight_endpoint_slot_count w hw C hu φ n hn N hnN _ _ hl
  have hd := linearWeight_canonicalEndpoints_mem_refinedDisk w hw C hu φ heven n hn
  exact hl.toPair_of_strip_count (by norm_num) n hnN hc hd.1 hd.2

/-- Lemma 25.4: the canonical H¹ pair, exact determinant occurrences, explicit radius, and gap bound. -/
theorem H1_canonical_periodic_localization
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    let w := SpectralWeight.piSobolev 1 (by norm_num)
    let x := canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven n
    let y := canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven n
    PeriodicEndpointPair (by simp) (weightedBaseToPair w φ) n x y ∧
    (∀ z ∈ resonantStrip n, resonantDeterminantExtension (by simp) w φ n z = 0 ↔ z = x ∨ z = y) ∧
    (∀ z ∈ resonantStrip n, analyticOrderNatAt (resonantDeterminantExtension (by simp) w φ n) z =
      ({x,y} : Multiset ℂ).count z) ∧
    ‖x-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧
    ‖y-(Real.pi:ℂ)*n‖ ≤ quadraticLocalizationRadius ‖φ‖ n ∧
    quadraticLocalizationRadius ‖φ‖ n < Real.pi/5 ∧
    ‖y-x‖^2 ≤ 6*resonantBProductSup (by simp) w φ n := by
  let w := SpectralWeight.piSobolev 1 (by norm_num)
  have hw : w.HasLinearFactor := SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl
  have hp := linearWeight_canonicalEndpointPair w hw Real.pi piSobolev_one_le_pi_bracket φ heven n hn
  have hl := linearWeight_canonicalEndpoints_localization w hw Real.pi piSobolev_one_le_pi_bracket φ heven n hn
  refine ⟨hp,?_,?_,hl.1,hl.2.1,quadraticLocalizationRadius_lt_pi_div_five (norm_nonneg _) n hn,hl.2.2⟩
  · intro z hz
    exact (mem_periodicSpectrum_iff_H1_determinant_zero φ n hn z hz).symm.trans (hp.spectrum_iff z hz)
  · intro z hz
    exact (linearWeight_analyticOrder_eq_periodicMultiplicity w hw Real.pi piSobolev_one_le_pi_bracket
      φ n hn z hz).trans (hp.multiplicity_eq_count z hz)

end NLS.ZakharovShabat
