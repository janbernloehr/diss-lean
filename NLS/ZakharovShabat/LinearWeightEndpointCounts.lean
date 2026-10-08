import NLS.ZakharovShabat.LinearWeightSpectralMultiplicity
import NLS.ZakharovShabat.PeriodicEndpointSlots

/-! # Counting endpoint occurrences in quantitative strips

The original canonical periodic product has total zero order two in each
quantitative strip. Any complete endpoint labeling therefore has exactly
two occurrences there, even when their spectral values coincide.
-/
noncomputable section
open scoped Classical
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The original canonical periodic product has zero count two on the entire quantitative strip. -/
theorem linearWeight_periodicProduct_strip_zeroCount (w : SpectralWeight) (hw : w.HasLinearFactor)
    (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    analyticZeroCount (canonicalPeriodicProduct (by simp) (weightedBaseToPair w φ)) (resonantStrip n) = 2 := by
  rw [analyticZeroCount_eq_sum
    (enclosedPeriodicSpectrum (by simp) (weightedBaseToPair w φ) ((Real.pi:ℂ)*n) (Real.pi/4))
    (fun z hz => refinedResonantDisk_subset_strip n
      ((mem_enclosedPeriodicSpectrum (by simp) _ _ z _).mp hz).2) (fun z hz => ?_)]
  · simp only [analyticOrderNatAt_canonicalPeriodicProduct (by simp) (by norm_num : (1:ENNReal) < 2)]
    exact linearWeight_sum_enclosed_multiplicity_two w hw C hu φ n hn
  · have hs := (canonicalPeriodicProduct_eq_zero_iff (by simp) (by norm_num : (1:ENNReal) < 2) _ z).mp hz.2
    exact (mem_enclosedPeriodicSpectrum (by simp) _ _ z _).mpr
      ⟨hs,(linearWeight_periodicSpectrum_localization w hw C hu φ n hn z hz.1 hs).2⟩

/-- A strip with index in the central block lies in its closed real-part bounds. -/
theorem abs_re_le_centralRadius_of_mem_resonantStrip (N : ℕ) (n : ℤ) (hn : n.natAbs ≤ N)
    (z : ℂ) (hz : z ∈ resonantStrip n) : |z.re| ≤ centralCircleRadius N := by
  have hindex : |(n:ℝ)| ≤ (N:ℝ) := by
    have h : (n.natAbs:ℝ) ≤ (N:ℝ) := by exact_mod_cast hn
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have ht := abs_add_le (z.re-Real.pi*n) (Real.pi*n)
  have he : (z.re-Real.pi*n)+(Real.pi*n) = z.re := by ring
  rw [he, abs_mul, abs_of_pos Real.pi_pos] at ht
  change |z.re-Real.pi*n| ≤ Real.pi/2 at hz
  unfold centralCircleRadius
  nlinarith [Real.pi_pos]

/-- Any complete central labeling has exactly two occurrences in a quantitative strip. -/
theorem linearWeight_endpoint_slot_count (w : SpectralWeight) (hw : w.HasLinearFactor)
    (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|))
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|)
    (N : ℕ) (hnN : n.natAbs ≤ N) (ξ η : ℤ → ℂ)
    (hl : PeriodicEndpointLabeling (by simp) (weightedBaseToPair w φ) N ξ η) :
    ((centralPeriodicSlots N).filter (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip n)).card = 2 := by
  rw [← hl.analyticZeroCount_eq_card_filter_slots (by norm_num : (1:ENNReal) < 2)
    (resonantStrip n) (abs_re_le_centralRadius_of_mem_resonantStrip N n hnN)]
  exact linearWeight_periodicProduct_strip_zeroCount w hw C hu φ n hn

end NLS.ZakharovShabat
