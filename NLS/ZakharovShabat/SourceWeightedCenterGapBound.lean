import NLS.ZakharovShabat.SourceResonantCenterGapBound
import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.ZakharovShabat.WeightedResonantCenterForget

/-! # Gap bounds in any available weighted realization

Forgetting a spectral weight preserves the actual diagonal center and both
off-diagonal values. The same real gap bound therefore holds in every
weighted realization of the original source.
-/

noncomputable section

namespace NLS.ZakharovShabat
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both weighted center values are bounded by twice the actual source gap. -/
theorem exists_sourceWeightedResonantCenter_gap_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (w : SpectralWeight) (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs →
      let ζ := weightedResonantDiagonalCenter hp w ψ n
      ‖weightedResonantBPlusExtension hp w ψ n ζ‖ ≤
        2 * ‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖ ∧
      ‖weightedResonantBMinusExtension hp w ψ n ζ‖ ≤
        2 * ‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖ := by
  obtain ⟨N₁,hN₁,hforget⟩ := exists_weightedResonantCenter_forget hp hp1 w ψ
  obtain ⟨N₂,_,U,_,hφU,hbound⟩ := exists_uniform_sourceResonantCenter_gap_bound hp hp1 φ.val
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro n hn
  have hf := hforget n (by omega)
  rw [hψ] at hf
  change ‖weightedResonantBPlusExtension hp w ψ n (weightedResonantDiagonalCenter hp w ψ n)‖ ≤ _ ∧
    ‖weightedResonantBMinusExtension hp w ψ n (weightedResonantDiagonalCenter hp w ψ n)‖ ≤ _
  rw [hf.2.1,hf.2.2]
  exact hbound φ.val hφU φ.property n (by omega)
end NLS.ZakharovShabat
