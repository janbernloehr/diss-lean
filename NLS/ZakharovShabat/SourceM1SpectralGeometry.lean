import NLS.ZakharovShabat.SourceH1CentralProductBound

/-! # Exact-cutoff source geometry for every M₁ spectral weight -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Both source endpoints lie in their π/5 disc at the original M₁ cutoff. -/
theorem sourceM1_endpoints_localization (w : SpectralWeight) (hw : w.HasLinearFactor)
    (ψ : CoeffPair 2) (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ) (n : ℤ)
    (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    ‖canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
      (Real.pi:ℂ)*n‖ ≤ Real.pi/5 ∧
    ‖canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
      (Real.pi:ℂ)*n‖ ≤ Real.pi/5 := by
  have heven : weightedBaseToPair w φ ∈ pairParitySubspace 0 := hφ ▸ periodOnePotential_mem ψ
  have h := M1_canonicalEndpoints_localization w hw φ heven n hn
  simp only [hφ] at h
  have hr := (quadraticLocalizationRadius_lt_pi_div_five (norm_nonneg φ) n hn).le
  exact ⟨h.1.trans hr,h.2.1.trans hr⟩

/-- The whole source gap has the same localization disc for an arbitrary M₁ weight. -/
theorem sourceM1_gap_point_localization (w : SpectralWeight) (hw : w.HasLinearFactor)
    (ψ : CoeffPair 2) (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ) (n : ℤ)
    (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ n) :
    ‖z-(Real.pi:ℂ)*n‖ ≤ Real.pi/5 := by
  have h := sourceM1_endpoints_localization w hw ψ φ hφ n hn
  exact gap_segment_norm_sub_le _ _ z _ _ h.1 h.2 hz

/-- Lowering the weight to its linear factor preserves the central strip boundary. -/
theorem sourceM1_central_endpoints (w : SpectralWeight) (hw : w.HasLinearFactor)
    (ψ : CoeffPair 2) (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (m : ℤ) (hm : m.natAbs < N) :
    |(canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re| ≤ ((N:ℝ)-1/2)*Real.pi ∧
    |(canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re| ≤ ((N:ℝ)-1/2)*Real.pi := by
  let v := SpectralWeight.sobolev 1 (by norm_num)
  let η := m1LinearInclusion w hw φ
  have hη : weightedBaseToPair v η = periodOnePotential ψ := by
    simpa only [v,η,weightedBaseToPair_m1LinearInclusion] using hφ
  have hpar : weightedBaseToPair v η ∈ pairParitySubspace 0 := hη ▸ periodOnePotential_mem ψ
  have hs (i : Fin 2) := abs_re_le_of_not_mem_exterior_strips N
    (periodicEndpointSlot
      (canonicalPeriodicLeft (by simp) (by norm_num) (weightedBaseToPair v η) hpar)
      (canonicalPeriodicRight (by simp) (by norm_num) (weightedBaseToPair v η) hpar) (toLex (m,i)))
    (fun n hn => linearWeight_canonicalSlot_not_mem_strip v
      (SpectralWeight.hasLinearFactor_sobolev 1 le_rfl) 1
      (by intro k; simp [v,Weight.sobolev_apply]) η hpar n
      (m1LinearInclusion_threshold w hw φ n (exterior_index_localization_threshold ‖φ‖ N hN n hn))
      m (by intro he; subst n; omega) i)
  exact ⟨by simpa only [periodicEndpointSlot_left,v,η,weightedBaseToPair_m1LinearInclusion,hφ] using hs 0,
    by simpa only [periodicEndpointSlot_right,v,η,weightedBaseToPair_m1LinearInclusion,hφ] using hs 1⟩

end NLS.ZakharovShabat
