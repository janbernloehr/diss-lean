import NLS.ZakharovShabat.SourceHilbertInfiniteCoveringDimension
import NLS.FunctionalAnalysis.CoveringDimensionValue
import NLS.FunctionalAnalysis.CircleProductCoveringDimensionLower

/-! # Numerical covering dimension for actual Hilbert isospectral sets

Infinite-gap sets have dimension infinity. Any finite covering-dimension
bound for a finite-gap set is at least its actual open-gap count, and a
finite-gap set with no open gaps has dimension zero. The matching finite
upper bound for a positive gap count remains separate.
-/
noncomputable section
set_option autoImplicit false
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The actual infinite-gap isospectral set has numerical covering dimension infinity. -/
theorem sourceHilbertInfiniteGap_coveringDimension_eq_top
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∉ sourceFiniteGapLocus (by simp) (by norm_num)) :
    coveringDimension (sourceIsospectralSet ENNReal.ofNat_ne_top φ) = ⊤ :=
  coveringDimension_eq_top_iff.mpr (sourceHilbertInfiniteGap_not_coveringDimensionLE φ hφ)

/-- Isospectral sets are nonempty, so their numerical covering dimension is nonnegative. -/
theorem sourceHilbertIsospectralSet_zero_le_coveringDimension
    (φ : realTypeSourceSubmodule 2) :
    (0 : WithBot ℕ∞) ≤ coveringDimension (sourceIsospectralSet ENNReal.ofNat_ne_top φ) := by
  obtain ⟨e⟩ := sourceHilbertIsospectralSet_homeomorphic_circles φ
  let : Nonempty (sourceIsospectralSet ENNReal.ofNat_ne_top φ) := ⟨e.symm (fun _ => 1)⟩
  exact zero_le_coveringDimension

/-- A covering-dimension bound for a finite-gap set is at least the number of its open gaps. -/
theorem sourceHilbertFiniteGap_gapCount_le_of_coveringDimensionLE
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) {n : ℕ}
    (h : HasCoveringDimensionLE (sourceIsospectralSet ENNReal.ofNat_ne_top φ) n) :
    Nat.card (sourceHilbertOpenGapIndex φ) ≤ n := by
  obtain ⟨e⟩ := sourceHilbertIsospectralSet_homeomorphic_finiteTorus φ hφ
  simpa only [Fintype.card_fin] using card_le_of_hasCoveringDimensionLE_circleProduct (h.homeomorph e)

/-- A finite-gap isospectral set with no open gaps has numerical covering dimension zero. -/
theorem sourceHilbertFiniteGap_coveringDimension_eq_zero
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hN : Nat.card (sourceHilbertOpenGapIndex φ) = 0) :
    coveringDimension (sourceIsospectralSet ENNReal.ofNat_ne_top φ) = 0 := by
  obtain ⟨e⟩ := sourceHilbertIsospectralSet_homeomorphic_finiteTorus φ hφ
  rw [coveringDimension_homeomorph e,hN]
  exact coveringDimension_eq_zero_of_subsingleton

end NLS.ZakharovShabat
