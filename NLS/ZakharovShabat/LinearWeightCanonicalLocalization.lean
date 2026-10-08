import NLS.ZakharovShabat.EndpointStripAnchors
import NLS.ZakharovShabat.LinearWeightEndpointCounts
import NLS.ZakharovShabat.UniformCanonicalPeriodicEndpoints

/-! # Canonical signed labels at the quadratic threshold

Distant canonical pairs anchor the two tails. Counting occurrences on each
successive strip propagates their signed labels inward to the exact threshold.
-/
noncomputable section
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The canonical pair with signed index n belongs to its quantitative refined disc. -/
theorem linearWeight_canonicalEndpoints_mem_refinedDisk (w : SpectralWeight) (hw : w.HasLinearFactor)
    (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|)) (φ : WeightedCoeffPair w.toWeight 2)
    (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven n ∈ refinedResonantDisk n ∧
    canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven n ∈ refinedResonantDisk n := by
  let ξ := canonicalPeriodicLeft (by simp) (by norm_num : (1:ENNReal) < 2) (weightedBaseToPair w φ) heven
  let η := canonicalPeriodicRight (by simp) (by norm_num : (1:ENNReal) < 2) (weightedBaseToPair w φ) heven
  let K := canonicalPeriodicCutoff (by simp) (by norm_num : (1:ENNReal) < 2) (weightedBaseToPair w φ) heven
  have hspec := canonicalPeriodicEndpoints_spec (by simp) (by norm_num : (1:ENNReal) < 2) (weightedBaseToPair w φ) heven
  obtain ⟨N₀,_,U,_,_,hφ,_,hlabels⟩ := exists_uniform_canonicalPeriodicEndpoints
    (by simp) (by norm_num : (1:ENNReal) < 2) w φ
  let A := max N₀ (max K n.natAbs)+1
  let N := A+1
  have hKA : K < A := by dsimp [A]; omega
  have hnA : n.natAbs ≤ A := by dsimp [A]; omega
  have hAN : A ≤ N := by dsimp [N]; omega
  have hN₀ : N₀ ≤ N := by dsimp [N,A]; omega
  have hl : PeriodicEndpointLabeling (by simp) (weightedBaseToPair w φ) N ξ η :=
    hlabels φ hφ heven N hN₀
  have hthreshold (m : ℤ) (hm : n.natAbs ≤ m.natAbs) : 8*‖φ‖^2 ≤ 1+|(m:ℝ)| := by
    have h : (n.natAbs:ℝ) ≤ (m.natAbs:ℝ) := by exact_mod_cast hm
    have h' : |(n:ℝ)| ≤ |(m:ℝ)| := by simpa only [Nat.cast_natAbs,Int.cast_abs] using h
    linarith
  have horder : Monotone (fun k : ℤ ×ₗ Fin 2 => (periodicEndpointSlot ξ η k).re) := by
    intro i j hij
    exact re_le_of_complexLexLE (periodicEndpointSlot_ordered ξ η hspec.2.1 hspec.2.2 i j hij)
  have hcount (m : ℤ) (hm : n.natAbs ≤ m.natAbs) (hmA : m.natAbs ≤ A) :=
    linearWeight_endpoint_slot_count w hw C hu φ m (hthreshold m hm) N (hmA.trans hAN) ξ η hl
  have hrefine (m : ℤ) (hm : n.natAbs ≤ m.natAbs) (_hmA : m.natAbs ≤ A)
      (hs : ξ m ∈ resonantStrip m ∧ η m ∈ resonantStrip m) :
      ξ m ∈ refinedResonantDisk m ∧ η m ∈ refinedResonantDisk m := by
    have hmem := canonicalPeriodicEndpoints_mem_spectrum (by simp) (by norm_num : (1:ENNReal) < 2)
      (weightedBaseToPair w φ) heven m
    exact ⟨(linearWeight_periodicSpectrum_localization w hw C hu φ m (hthreshold m hm) _ hs.1 hmem.1).2,
      (linearWeight_periodicSpectrum_localization w hw C hu φ m (hthreshold m hm) _ hs.2 hmem.2).2⟩
  have hanchor (m : ℤ) (hm : K < m.natAbs) :
      ξ m ∈ refinedResonantDisk m ∧ η m ∈ refinedResonantDisk m :=
    ⟨(hspec.1.distant m hm).left_mem,(hspec.1.distant m hm).right_mem⟩
  exact endpoint_pair_refined_of_anchors N A n ξ η hnA hAN horder hcount hrefine
    (hanchor A (by simpa using hKA)) (hanchor (-(A:ℤ)) (by simpa using hKA))

/-- The explicit radius and factor-six gap bound hold for the canonical signed endpoints. -/
theorem linearWeight_canonicalEndpoints_localization (w : SpectralWeight) (hw : w.HasLinearFactor)
    (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|)) (φ : WeightedCoeffPair w.toWeight 2)
    (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    ‖canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven n-(Real.pi:ℂ)*n‖ ≤
      quadraticLocalizationRadius ‖φ‖ n ∧
    ‖canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven n-(Real.pi:ℂ)*n‖ ≤
      quadraticLocalizationRadius ‖φ‖ n ∧
    ‖canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven n-
      canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖^2 ≤
        6*resonantBProductSup (by simp) w φ n := by
  have hd := linearWeight_canonicalEndpoints_mem_refinedDisk w hw C hu φ heven n hn
  have hs := canonicalPeriodicEndpoints_mem_spectrum (by simp) (by norm_num : (1:ENNReal) < 2)
    (weightedBaseToPair w φ) heven n
  have hx := refinedResonantDisk_subset_strip n hd.1
  have hy := refinedResonantDisk_subset_strip n hd.2
  exact ⟨(linearWeight_periodicSpectrum_localization w hw C hu φ n hn _ hx hs.1).1,
    (linearWeight_periodicSpectrum_localization w hw C hu φ n hn _ hy hs.2).1,
    linearWeight_periodicSpectrum_gap_le w hw C hu φ n hn _ _ hy hx hs.2 hs.1⟩

end NLS.ZakharovShabat
