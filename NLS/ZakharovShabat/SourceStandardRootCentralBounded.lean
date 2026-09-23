import NLS.ZakharovShabat.SourceStandardRootCentralBounds

/-!
# Bounded-radius central standard-root estimates

The finite central-block estimate remains valid after shrinking every
central disc by the same positive margin. This allows its radius to
match the quarter-π requirement of the mixed-pair geometry.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A smaller enlargement margin gives a subset of the original
central midpoint disc. -/
theorem sourceClusterDisc_mono_constant_margin
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (ε δ : ℝ) (hεδ : ε ≤ δ) (n : ℤ) :
    sourceClusterDisc hp hp1 φ (fun _ => ε) n ⊆
      sourceClusterDisc hp hp1 φ (fun _ => δ) n := by
  intro z hz
  simp only [sourceClusterDisc, mem_ball] at hz ⊢
  exact lt_of_lt_of_le hz (by linarith)

/-- The central-block form of (2.10) may use any prescribed positive
upper bound on its enlargement margin. -/
theorem exists_local_source_central_root_index_bounds_bounded
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) (B : ℝ) (hB : 0 < B) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ B ∧ ∃ c : ℝ, 1 ≤ c ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∀ ψ ∈ V, ∀ m n : ℤ, m.natAbs ≤ N → n.natAbs ≤ N → m ≠ n →
          ∀ z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) m,
            c⁻¹*|((m-n : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ ∧
              ‖sourceStandardRoot hp hp1 ψ n z‖ ≤
                c*|((m-n : ℤ) : ℝ)| := by
  obtain ⟨δ, hδ, c, hc, V, hVo, hVc, hφV, hroot⟩ :=
    exists_local_source_central_root_index_bounds hp hp1 φ hφ N
  let ε := min δ B
  have hε : 0 < ε := lt_min hδ hB
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεB : ε ≤ B := min_le_right _ _
  refine ⟨ε, hε, hεB, c, hc, V, hVo, hVc, hφV, ?_⟩
  intro ψ hψ m n hm hn hmn z hz
  exact hroot ψ hψ m n hm hn hmn z
    (sourceClusterDisc_mono_constant_margin hp hp1 φ ε δ hεδ m hz)

end NLS.ZakharovShabat
