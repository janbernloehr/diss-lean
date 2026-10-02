import NLS.ZakharovShabat.WeightedResonantCenterForget
import NLS.ZakharovShabat.SourceFiniteGapAdaptedCoordinates

/-! # Finite-gap closing equations in every available spectral weight

A weighted realization of the original period-one source has the same
actual distant centers and closing equations. Thus spectral finite-gap
support forces the weighted remainder to equal the negative leading
Fourier tail, not merely an abstract coordinate surrogate.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite-gap closing equations persist in any spectral weight
for which the same original source has a weighted realization. -/
theorem exists_sourceFiniteGap_weighted_center_closed
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1)
    (w : SpectralWeight) (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs →
      weightedResonantBPlusExtension hp w ψ n (weightedResonantDiagonalCenter hp w ψ n) = 0 ∧
      weightedResonantBMinusExtension hp w ψ n (weightedResonantDiagonalCenter hp w ψ n) = 0 := by
  obtain ⟨N₁,hN₁,hforget⟩ := exists_weightedResonantCenter_forget hp hp1 w ψ
  obtain ⟨N₂,hclosed⟩ := (sourceFiniteGapLocus_iff_eventually_center_closed hp hp1 φ).mp hfinite
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro n hn
  have hf := hforget n (by omega)
  rw [hψ] at hf
  exact ⟨hf.2.1.trans (hclosed n (by omega)).1,hf.2.2.trans (hclosed n (by omega)).2⟩

/-- The actual weighted remainder is exactly the negative leading
Fourier tail at every sufficiently large cutoff. -/
theorem sourceFiniteGap_weighted_remainder_eq_neg_leading
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1)
    (w : SpectralWeight) (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ M : ℕ, N ≤ M →
      weightedResonantCenterRemainder hp w ψ M = -weightedResonantLeadingTail w ψ M := by
  obtain ⟨N,hN,hclosed⟩ := exists_sourceFiniteGap_weighted_center_closed hp hp1 φ hfinite w ψ hψ
  refine ⟨N,hN,?_⟩
  intro M hM
  have hcoord (positive : Bool) : weightedResonantCenterRemainderCoordinate hp w ψ M positive =
      fun n => -weightedResonantLeadingTailCoordinate w ψ M positive n := by
    funext n
    by_cases hn : M ≤ n.natAbs
    · have hc := hclosed n (hM.trans hn)
      cases positive <;>
        simp [weightedResonantCenterRemainderCoordinate,weightedResonantLeadingTailCoordinate,hn,hc]
    · simp [weightedResonantCenterRemainderCoordinate,weightedResonantLeadingTailCoordinate,hn]
  have hmem (positive : Bool) : Memℓp (weightedResonantCenterRemainderCoordinate hp w ψ M positive) p := by
    rw [hcoord]
    exact (weightedResonantLeadingTailCoordinate_mem hp w ψ M positive).neg
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n
  · change (weightedResonantCenterRemainder hp w ψ M).fst n = -(weightedResonantLeadingTail w ψ M).fst n
    rw [(weightedResonantCenterRemainder_apply_of_mem hp w ψ M hmem n).1,hcoord]
    exact congrArg Neg.neg (weightedResonantLeadingTail_fst hp w ψ M n).symm
  · change (weightedResonantCenterRemainder hp w ψ M).snd n = -(weightedResonantLeadingTail w ψ M).snd n
    rw [(weightedResonantCenterRemainder_apply_of_mem hp w ψ M hmem n).2,hcoord]
    exact congrArg Neg.neg (weightedResonantLeadingTail_snd hp w ψ M n).symm

end NLS.ZakharovShabat
