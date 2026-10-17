import NLS.ZakharovShabat.SourceWeightedRealSpaces
import NLS.ZakharovShabat.NormalizedWeightedClosingApproximation

/-! # Density of actual finite-gap sources in every weighted real space

The constructed normalized closing approximation gives nearby real
sources whose original spectra have only finitely many open gaps.
The real weight equivalence preserves norms and transfers density to
the native weighted source topology for every spectral weight.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual finite-gap sources approximate every real source in the native weighted norm. -/
theorem exists_weightedRealSource_finiteGap_norm_sub_lt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) (ε : ℝ) (hε : 0 < ε) :
    ∃ b : weightedRealSourceSubmodule (p := p) w,
      originalWeightedRealSource w b ∈ sourceFiniteGapLocus hp hp1 ∧ ‖b-a‖ < ε := by
  let φ := weightedRealSourceEquiv w a
  obtain ⟨N,_,ψ,hψ,hclose,_,hclosed⟩ := exists_real_normalizedWeightedClosingApproximation
    hp hp1 w φ.val φ.property ε hε
  let ξ : realTypeSourceSubmodule p := ⟨ψ,hψ⟩
  let b := (weightedRealSourceEquiv w).symm ξ
  have hb : weightedRealSourceEquiv w b = ξ := (weightedRealSourceEquiv w).apply_symm_apply ξ
  refine ⟨b,?_,?_⟩
  · unfold originalWeightedRealSource
    rw [hb]
    exact normalizedWeightedSource_finiteGap_of_closed hp hp1 w ψ hψ N hclosed
  · rw [← norm_weightedRealSourceEquiv w (b-a),map_sub,hb]
    exact hclose

private theorem dense_of_norm_approximation
    {E : Type*} [NormedAddCommGroup E] (S : Set E)
    (h : ∀ a : E, ∀ ε : ℝ, 0 < ε → ∃ b ∈ S, ‖b-a‖ < ε) : Dense S := by
  apply Metric.dense_iff.mpr
  intro a ε hε
  obtain ⟨b,hb,hclose⟩ := h a ε hε
  exact ⟨b,by simpa only [mem_ball,dist_eq_norm] using hclose,hb⟩

/-- Finite-gap sources are dense in normalized weighted real coordinates. -/
theorem dense_normalizedWeightedRealSource_finiteGap (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) :
    Dense {a : realTypeSourceSubmodule p |
      normalizedWeightedRealSourceLp w a ∈ sourceFiniteGapLocus hp hp1} := by
  apply dense_of_norm_approximation
  intro a ε hε
  obtain ⟨N,_,ψ,hψ,hclose,_,hclosed⟩ := exists_real_normalizedWeightedClosingApproximation
    hp hp1 w a.val a.property ε hε
  exact ⟨⟨ψ,hψ⟩,normalizedWeightedSource_finiteGap_of_closed hp hp1 w ψ hψ N hclosed,hclose⟩

/-- Finite-gap sources are dense in every native weighted real source space. -/
theorem dense_weightedRealSource_finiteGap (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) :
    Dense {a : weightedRealSourceSubmodule (p := p) w |
      originalWeightedRealSource w a ∈ sourceFiniteGapLocus hp hp1} :=
  (dense_normalizedWeightedRealSource_finiteGap hp hp1 w).preimage (weightedRealSourceEquiv w).isOpenMap
end NLS.ZakharovShabat
