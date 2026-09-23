import NLS.ZakharovShabat.SourceStandardRootMixedBounds

/-!
# Local two-sided mixed central-tail root estimates

A connected source neighborhood is constructed from uniform tail
isolation and finite central-disc isolation. Strict localization of
both outer endpoints makes the mixed root bounds uniform for every
nearby source and both mixed index orientations.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A connected local neighborhood supports equation (2.10) for every
central/tail pair in both index orientations. -/
theorem exists_local_source_mixed_root_bounds
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ c : ℝ, 1 ≤ c ∧
        ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
          ∀ ψ ∈ V, ∀ (i j : ℤ), i.natAbs ≤ N → N < j.natAbs →
            (∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
              c⁻¹*|((i-j : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ j z‖ ∧
              ‖sourceStandardRoot hp hp1 ψ j z‖ ≤ c*|((i-j : ℤ) : ℝ)|) ∧
            (∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε j,
              c⁻¹*|((i-j : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ i z‖ ∧
              ‖sourceStandardRoot hp hp1 ψ i z‖ ≤ c*|((i-j : ℤ) : ℝ)|) := by
  obtain ⟨N₀, Ut, hUto, hφt, htail⟩ :=
    exists_uniform_source_tail_isolation hp hp1 φ
  let N := N₀ + 1
  have hN₀ : N₀ < N := by dsimp [N]; omega
  have hpos : N₀ < (N : ℤ).natAbs := by simpa using hN₀
  have hneg : N₀ < (-(N : ℤ)).natAbs := by simpa using hN₀
  have houterR := (htail φ hφt (N : ℤ) hpos).2.1
  have houterL := (htail φ hφt (-(N : ℤ)) hneg).1
  obtain ⟨ε, hε, hεmax, Uc, hUco, hφc, hcentral, _⟩ :=
    exists_local_sourceClusterDiscs_finite_block_bounded hp hp1 φ hφ
      (Finset.Icc (-(N : ℤ)) (N : ℤ))
      (by positivity : 0 < Real.pi/4)
  have hcluster : ∀ ψ ∈ Uc ∩ Ut, ∀ n : ℤ,
      sourceSpectralCluster hp hp1 ψ n ⊆
        sourceIsolatingDisc hp hp1 φ N ε n := by
    intro ψ hψ n
    by_cases hn : n.natAbs ≤ N
    · simp only [sourceIsolatingDisc, if_pos hn]
      have hmem : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      exact hcentral ψ hψ.1 n hmem
    · simp only [sourceIsolatingDisc, if_neg hn]
      have hnt : N₀ < n.natAbs := by omega
      intro z hz
      obtain ⟨hL, hR, hD, hN, hC⟩ := htail ψ hψ.2 n hnt
      rcases hz with h | h | h | h | h
      · rw [h]; exact hL
      · rw [h]; exact hR
      · rw [h]; exact hD
      · rw [h]; exact hN
      · rw [h]; exact hC
  obtain ⟨c, hc, hbound⟩ :=
    exists_source_central_tail_root_bounds hp hp1 φ hφ N ε
      hε.le hεmax houterL houterR
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp
    ((hUco.inter hUto).mem_nhds ⟨hφc, hφt⟩)
  refine ⟨N, ε, hε, hεmax, c, hc, ball φ r, Metric.isOpen_ball,
    isConnected_ball hr, mem_ball_self hr, ?_⟩
  intro ψ hψ i j hi hj
  have hψU : ψ ∈ Uc ∩ Ut := hrU hψ
  obtain ⟨hfirst, hsecond⟩ := hbound ψ (hcluster ψ hψU) i j hi hj
  constructor
  · intro z hz
    exact hfirst z (by simpa only [sourceIsolatingDisc, if_pos hi] using hz)
  · intro z hz
    have hnj : ¬ j.natAbs ≤ N := by omega
    exact hsecond z (by simpa only [sourceIsolatingDisc, if_neg hnj] using hz)

end NLS.ZakharovShabat
