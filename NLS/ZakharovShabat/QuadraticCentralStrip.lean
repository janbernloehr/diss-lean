import NLS.ZakharovShabat.QuadraticCanonicalPeriodicPair

/-! # The remaining canonical eigenvalues lie in the central strip

Two endpoint occurrences exhaust every quantitative strip, so no other
signed slot can enter it. Covering the plane by these strips gives the
printed quadratic real-part bound for all remaining indices.
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- Once the two n-slots occupy a two-occurrence strip, a differently indexed slot cannot enter. -/
theorem endpoint_slot_not_mem_strip_of_two (N : ℕ) (ξ η : ℤ → ℂ)
    (n m : ℤ) (i : Fin 2) (hn : n.natAbs ≤ N) (hm : m.natAbs ≤ N) (hmn : m ≠ n)
    (hc : ((centralPeriodicSlots N).filter (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip n)).card = 2)
    (hx : ξ n ∈ resonantStrip n) (hy : η n ∈ resonantStrip n) :
    periodicEndpointSlot ξ η (toLex (m,i)) ∉ resonantStrip n := by
  have hleft : toLex (n,0) ∈ (centralPeriodicSlots N).filter
      (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip n) :=
    Finset.mem_filter.mpr ⟨by simpa using hn,by simpa using hx⟩
  have hright : toLex (n,1) ∈ (centralPeriodicSlots N).filter
      (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip n) :=
    Finset.mem_filter.mpr ⟨by simpa using hn,by simpa using hy⟩
  have hd (j : Fin 2) : toLex (m,i) ≠ toLex (n,j) := by
    intro h
    exact hmn (congrArg (fun k : ℤ ×ₗ Fin 2 => (ofLex k).1) h)
  intro hz
  exact NLS.not_mem_of_card_two _ hc hleft hright (hd 0) (hd 1)
    (by simp) (Finset.mem_filter.mpr ⟨by simpa using hm,hz⟩)

/-- The explicit canonical strip contains no occurrence belonging to another signed index. -/
theorem linearWeight_canonicalSlot_not_mem_strip (w : SpectralWeight) (hw : w.HasLinearFactor)
    (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|)) (φ : WeightedCoeffPair w.toWeight 2)
    (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) (m : ℤ) (hmn : m ≠ n) (i : Fin 2) :
    periodicEndpointSlot
      (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven)
      (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven)
      (toLex (m,i)) ∉ resonantStrip n := by
  obtain ⟨N₀,_,U,_,_,hφ,_,hlabels⟩ := exists_uniform_canonicalPeriodicEndpoints
    (by simp) (by norm_num : (1:ENNReal) < 2) w φ
  let N := max N₀ (max n.natAbs m.natAbs)
  have hl := hlabels φ hφ heven N (le_max_left _ _)
  have hnN : n.natAbs ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hmN : m.natAbs ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  have hc := linearWeight_endpoint_slot_count w hw C hu φ n hn N hnN _ _ hl
  have hd := linearWeight_canonicalEndpoints_mem_refinedDisk w hw C hu φ heven n hn
  exact endpoint_slot_not_mem_strip_of_two N _ _ n m i hnN hmN hmn hc
    (refinedResonantDisk_subset_strip n hd.1) (refinedResonantDisk_subset_strip n hd.2)

/-- Excluding every strip past a real threshold gives the exact central real-part bound. -/
theorem abs_re_lt_of_not_mem_quantitative_strips (R : ℝ) (z : ℂ)
    (h : ∀ n : ℤ, R ≤ 1+|(n:ℝ)| → z ∉ resonantStrip n) :
    |z.re| < (R-1/2)*Real.pi := by
  obtain ⟨n,hn⟩ := exists_centered_real_part z
  have hz : z ∈ resonantStrip n := hn
  have hnR : 1+|(n:ℝ)| < R := lt_of_not_ge (fun hh => h n hh hz)
  have hbound : |z.re| ≤ Real.pi/2+Real.pi*|(n:ℝ)| := by
    calc
      |z.re| = |(z.re-Real.pi*n)+Real.pi*n| := by congr 1; ring
      _ ≤ |z.re-Real.pi*n|+|Real.pi*n| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul,abs_of_pos Real.pi_pos]; linarith
  nlinarith [Real.pi_pos]

/-- Both remaining canonical endpoints satisfy the strict central real-part bound. -/
theorem linearWeight_canonicalEndpoints_central_re (w : SpectralWeight) (hw : w.HasLinearFactor)
    (C : ℝ) (hu : ∀ k : ℤ, w k ≤ C*(1+|(k:ℝ)|)) (φ : WeightedCoeffPair w.toWeight 2)
    (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (m : ℤ) (hm : 1+|(m:ℝ)| < 8*‖φ‖^2) :
    |(canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven m).re| < (8*‖φ‖^2-1/2)*Real.pi ∧
    |(canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven m).re| < (8*‖φ‖^2-1/2)*Real.pi := by
  have h (i : Fin 2) := abs_re_lt_of_not_mem_quantitative_strips (8*‖φ‖^2)
    (periodicEndpointSlot
      (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair w φ) heven)
      (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair w φ) heven) (toLex (m,i)))
    (fun n hn => linearWeight_canonicalSlot_not_mem_strip w hw C hu φ heven n hn m
      (by intro he; subst n; linarith) i)
  exact ⟨by simpa only [periodicEndpointSlot_left] using h 0,
    by simpa only [periodicEndpointSlot_right] using h 1⟩

end NLS.ZakharovShabat
