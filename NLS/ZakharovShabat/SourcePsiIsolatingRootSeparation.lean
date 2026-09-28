import NLS.ZakharovShabat.SourceGlobalIsolation
import NLS.ZakharovShabat.SourcePsiNearFreeRegularAnalytic

/-!
# Selected roots in disjoint isolating discs

The domain Ωᵖ of the dissertation places each selected root in its
assigned spectral neighborhood. When these neighborhoods isolate the
periodic gaps pairwise, every other root stays off a selected gap.
This is the finite-index nonvanishing condition in Lemma 12.5.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Root localization in the assigned pairwise disjoint discs keeps
all retained roots other than the selected one off its periodic gap. -/
theorem sourcePsi_otherRoots_avoid_periodicSegment_of_isolatingDiscs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ) (a : Coeff p)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hroots : ∀ k : ℤ,
      displacedRoots a k ∈ sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ m k : ℤ, m ≠ k →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
        (sourceIsolatingDisc hp hp1 φ N ε k)) :
    ∀ m : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ m,
      ∀ k : ℤ, k ≠ m → z ≠ displacedRoots a k := by
  intro m z hz k hkm heq
  have hzDisc := hseg m hz
  have hkDisc := hroots k
  rw [← heq] at hkDisc
  exact Set.disjoint_left.mp (hdisjoint m k (Ne.symm hkm)) hzDisc hkDisc

/-- In particular, all other selected roots avoid the affine standard
root gap used in the psi diagonal variation formula. -/
theorem sourcePsi_otherRoots_avoid_standardGap_of_isolatingDiscs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ) (a : Coeff p)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hroots : ∀ k : ℤ,
      displacedRoots a k ∈ sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ m k : ℤ, m ≠ k →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
        (sourceIsolatingDisc hp hp1 φ N ε k)) :
    ∀ m : ℤ, ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m),
        ∀ k : ℤ, k ≠ m → z ≠ displacedRoots a k := by
  intro m z hz k hkm
  exact sourcePsi_otherRoots_avoid_periodicSegment_of_isolatingDiscs
    hp hp1 φ ψ N ε a hseg hroots hdisjoint m z
      (sourceStandardRoot_gapSegment_subset_periodicSegment hp hp1 ψ m hz)
      k hkm

/-- If each selected contour also stays inside its assigned disc,
the omitted root cannot lie on any other selected contour. -/
theorem sourcePsi_deletedRoot_avoids_otherCircle_of_isolatingDiscs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (a : Coeff p)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hcircle : ∀ m : ℤ,
      sphere (c m) (R m) ⊆
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hroots : ∀ k : ℤ,
      displacedRoots a k ∈ sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ m k : ℤ, m ≠ k →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
        (sourceIsolatingDisc hp hp1 φ N ε k)) :
    ∀ m n : ℤ, m ≠ n → ∀ z ∈ sphere (c m) (R m),
      z ≠ displacedRoots a n := by
  intro m n hmn z hz heq
  have hzDisc := hcircle m hz
  have hnDisc := hroots n
  rw [← heq] at hnDisc
  exact Set.disjoint_left.mp (hdisjoint m n hmn) hzDisc hnDisc

end NLS.ZakharovShabat
