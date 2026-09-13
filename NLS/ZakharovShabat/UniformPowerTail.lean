import NLS.ZakharovShabat.WeightedContraction

/-!
# Locally uniform smallness of power-tail estimates

A norm bound and one Fourier-tail bound define an open convex neighborhood
containing the potential and zero. On that neighborhood the power-tail
expressions from Lemma 6.8 become arbitrarily small at all larger cutoffs.
-/

noncomputable section
open scoped ENNReal Topology
open Filter
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform decay for the scalar budget used in both coefficient summability estimates. -/
theorem exists_uniform_powerTail_budget (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) {β δ C ε : ℝ}
    (hβ : 0 < β) (hδ : 0 < δ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ‖ψ‖ < ‖φ‖ + 1) ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        C * ((‖φ‖+1)^β / (N : ℝ)^δ + ‖weightedPairFourierTail w.toWeight (N/2) ψ‖^β) < ε := by
  let M := ‖φ‖ + 1
  let r := (ε / (2*(C+1)))^(1/β)
  have hM : 0 < M := by dsimp [M]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hrpow : r^β = ε / (2*(C+1)) := by
    dsimp [r]
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hβ.ne', Real.rpow_one]
  have ht := (tendsto_weightedPairFourierTail hp w.toWeight φ).norm
  simp only [norm_zero] at ht
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually_lt_const hr)
  have hrec : Tendsto (fun N : ℕ => M^β / (N : ℝ)^δ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop)
  obtain ⟨L, hL⟩ := eventually_atTop.mp (hrec.eventually_lt_const (Real.rpow_pos_of_pos hr β))
  let U := weightedFrequencyNeighborhood (p := p) w K M r
  refine ⟨max (2*K) (max 2 L), (le_max_left 2 L).trans (le_max_right _ _), U,
    isOpen_weightedFrequencyNeighborhood w K M r, convex_weightedFrequencyNeighborhood w K M r,
    ?_, ?_, ?_, ?_⟩
  · exact (mem_weightedFrequencyNeighborhood w K M r φ).mpr ⟨by dsimp [M]; linarith, hK K le_rfl⟩
  · exact (mem_weightedFrequencyNeighborhood w K M r 0).mpr (by simpa using And.intro hM hr)
  · intro ψ hψ
    exact ((mem_weightedFrequencyNeighborhood w K M r ψ).mp hψ).1
  · intro ψ hψ N hN
    have htail : ‖weightedPairFourierTail w.toWeight (N/2) ψ‖ ≤ r :=
      (norm_weightedPairFourierTail_antitone hp w.toWeight ψ (by omega : K ≤ N/2)).trans
        ((mem_weightedFrequencyNeighborhood w K M r ψ).mp hψ).2.le
    calc
      _ ≤ C * (r^β + r^β) := mul_le_mul_of_nonneg_left
        (add_le_add (hL N (by omega)).le (Real.rpow_le_rpow (norm_nonneg _) htail hβ.le)) hC
      _ < (C+1) * (r^β + r^β) := mul_lt_mul_of_pos_right (by linarith) (by positivity)
      _ = ε := by rw [hrpow]; field_simp; ring

end NLS.ZakharovShabat
