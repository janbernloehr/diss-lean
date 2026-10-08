import NLS.ZakharovShabat.SourceH1ExteriorProductBound

/-! # Central endpoints at an integer H¹ cutoff -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Integer strip exclusion gives the sharper half-step central boundary. -/
theorem abs_re_le_of_not_mem_exterior_strips (N : ℕ) (z : ℂ)
    (h : ∀ n : ℤ, N ≤ n.natAbs → z ∉ resonantStrip n) :
    |z.re| ≤ ((N:ℝ)-1/2)*Real.pi := by
  obtain ⟨n,hn⟩ := exists_centered_real_part z
  have hnN : n.natAbs < N := lt_of_not_ge (fun hh => h n hh hn)
  have hcast : (n.natAbs:ℝ)+1 ≤ (N:ℝ) := by exact_mod_cast hnN
  simp only [Nat.cast_natAbs,Int.cast_abs] at hcast
  have hbound : |z.re| ≤ Real.pi/2+Real.pi*|(n:ℝ)| := by
    calc
      |z.re| = |(z.re-Real.pi*n)+Real.pi*n| := by congr 1; ring
      _ ≤ |z.re-Real.pi*n|+|Real.pi*n| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul,abs_of_pos Real.pi_pos]; linarith
  nlinarith [Real.pi_pos]

/-- All central H¹ endpoints lie between ±(N-1/2)π at every valid cutoff. -/
theorem H1_canonicalEndpoints_cutoff_central_re
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (m : ℤ) (hm : m.natAbs < N) :
    |(canonicalPeriodicLeft (by simp) (by norm_num)
      (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) heven m).re| ≤ ((N:ℝ)-1/2)*Real.pi ∧
    |(canonicalPeriodicRight (by simp) (by norm_num)
      (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) heven m).re| ≤ ((N:ℝ)-1/2)*Real.pi := by
  have h (i : Fin 2) := abs_re_le_of_not_mem_exterior_strips N
    (periodicEndpointSlot
      (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) heven)
      (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ) heven)
      (toLex (m,i)))
    (fun n hn => linearWeight_canonicalSlot_not_mem_strip _
      (SpectralWeight.hasLinearFactor_piSobolev 1 le_rfl) Real.pi piSobolev_one_le_pi_bracket φ heven n
      (exterior_index_localization_threshold ‖φ‖ N hN n hn) m (by intro he; subst n; omega) i)
  exact ⟨by simpa only [periodicEndpointSlot_left] using h 0,
    by simpa only [periodicEndpointSlot_right] using h 1⟩

end NLS.ZakharovShabat
