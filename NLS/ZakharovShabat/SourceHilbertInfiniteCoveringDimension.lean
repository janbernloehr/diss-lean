import NLS.ZakharovShabat.SourceHilbertCoveringDimensionReduction
import NLS.FunctionalAnalysis.CubeCoveringDimensionLower

/-! # Infinite covering dimension of actual infinite-gap isospectral sets

Closed finite cubes in the actual Hilbert isospectral set and the numerical
cube lower bound rule out every finite covering-dimension bound.
-/
noncomputable section
set_option autoImplicit false
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Every infinite-gap Hilbert isospectral set has infinite covering dimension. -/
theorem sourceHilbertInfiniteGap_not_coveringDimensionLE
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∉ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℕ) :
    ¬ HasCoveringDimensionLE (sourceIsospectralSet ENNReal.ofNat_ne_top φ) n :=
  sourceHilbertInfiniteGap_not_coveringDimensionLE_of_cube φ hφ n
    (not_hasCoveringDimensionLE_cube n)

/-- No natural number bounds the standard covering dimension of an infinite-gap set. -/
theorem sourceHilbertInfiniteGap_no_finite_covering_dimension
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∉ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ¬ ∃ n : ℕ, HasCoveringDimensionLE (sourceIsospectralSet ENNReal.ofNat_ne_top φ) n := by
  rintro ⟨n,hn⟩
  exact sourceHilbertInfiniteGap_not_coveringDimensionLE φ hφ n hn

end NLS.ZakharovShabat
