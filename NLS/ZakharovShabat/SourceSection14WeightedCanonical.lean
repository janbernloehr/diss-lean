import NLS.ZakharovShabat.SourceBirkhoffWeightedScalarAnalytic
import NLS.ZakharovShabat.SourceSection14

/-! # Section 14 canonical coordinates on every weighted real source

The constructed map has scalar complex analytic extensions on a common
open weighted domain containing every weighted real source. Their actual
derivatives satisfy the physical canonical relations for all spectral
weights and all finite p>1. Sequence-valued weighted analyticity and the
weighted local and global inverse assertions remain separate obligations.
-/
noncomputable section
open Set NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]


/-- An actual Section 14 construction satisfies the canonical identities on every
native weighted real source, with no canonicality or derivative premises. -/
theorem sourceSection14_weighted_canonical (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ _D : SourceSection14Data hp hp1 W₀ W V s, ∀ w : SpectralWeight,
        ∀ a : weightedRealSourceSubmodule (p := p) w,
          ∃ X Y : ℤ → WeightedRegularSourceCotangent (sourceFrequencyWeight w) p,
            (∀ n, (X n).toCotangent = fderiv ℂ (originalWeightedBirkhoffX hp hp1 s w n) a.val ∧
              (Y n).toCotangent = fderiv ℂ (originalWeightedBirkhoffY hp hp1 s w n) a.val) ∧
            ∀ n m, (X n).bivector (X m) = 0 ∧
              (X n).bivector (Y m) = -(if n = m then 1 else 0) ∧ (Y n).bivector (Y m) = 0 := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 hp hp1
  exact ⟨W₀,W,V,s,D,fun w a => D.complex.originalWeightedBirkhoff_canonical w a⟩

end NLS.ZakharovShabat
