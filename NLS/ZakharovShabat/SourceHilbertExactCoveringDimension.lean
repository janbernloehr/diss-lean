import NLS.FunctionalAnalysis.CircleProductCoveringDimension
import NLS.ZakharovShabat.SourceHilbertCoveringDimensionValue

/-! # Exact covering dimension equals the number of actual open gaps

The dimension is the finite open-gap count in the finite-gap case and
infinity in the infinite-gap case. The equality is transported through
the established homeomorphism in the original Hilbert topology.
-/
noncomputable section
set_option autoImplicit false
open Filter NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Every actual Hilbert isospectral set has dimension equal to its extended open-gap count. -/
theorem sourceHilbertIsospectralSet_coveringDimension_eq_gapCount
    (φ : realTypeSourceSubmodule 2) :
    coveringDimension (sourceIsospectralSet ENNReal.ofNat_ne_top φ) =
      (ENat.card (sourceHilbertOpenGapIndex φ) : WithBot ℕ∞) := by
  obtain ⟨e⟩ := sourceHilbertIsospectralSet_homeomorphic_circles φ
  rw [coveringDimension_homeomorph e,coveringDimension_circleProduct_eq_card]

/-- In the finite-gap case, numerical covering dimension is the actual number of open gaps. -/
theorem sourceHilbertFiniteGap_coveringDimension_eq_gapCount
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    coveringDimension (sourceIsospectralSet ENNReal.ofNat_ne_top φ) =
      (Nat.card (sourceHilbertOpenGapIndex φ) : WithBot ℕ∞) := by
  obtain ⟨e⟩ := sourceHilbertIsospectralSet_homeomorphic_finiteTorus φ hφ
  rw [coveringDimension_homeomorph e,coveringDimension_circleProduct,Fintype.card_fin]

/-- Finite covering-dimension bounds on a finite-gap set are exactly the bounds on its gap count. -/
theorem sourceHilbertFiniteGap_coveringDimensionLE_iff
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℕ) :
    HasCoveringDimensionLE (sourceIsospectralSet ENNReal.ofNat_ne_top φ) n ↔
      Nat.card (sourceHilbertOpenGapIndex φ) ≤ n := by
  obtain ⟨e⟩ := sourceHilbertIsospectralSet_homeomorphic_finiteTorus φ hφ
  rw [hasCoveringDimensionLE_homeomorph_iff e,hasCoveringDimensionLE_circleProduct_iff,Fintype.card_fin]

/-- Infinite covering dimension is equivalent to having infinitely many actual open gaps. -/
theorem sourceHilbertIsospectralSet_coveringDimension_eq_top_iff
    (φ : realTypeSourceSubmodule 2) :
    coveringDimension (sourceIsospectralSet ENNReal.ofNat_ne_top φ) = ⊤ ↔
      φ ∉ sourceFiniteGapLocus (by simp) (by norm_num) := by
  constructor
  · intro h hφ
    exact (coveringDimension_eq_top_iff.mp h) _
      ((sourceHilbertFiniteGap_coveringDimensionLE_iff φ hφ _).mpr le_rfl)
  · exact sourceHilbertInfiniteGap_coveringDimension_eq_top φ

/-- Infinite covering dimension occurs for residual actual real Hilbert sources. -/
theorem eventually_residual_sourceHilbertIsospectralSet_infinite_coveringDimension :
    ∀ᶠ φ : realTypeSourceSubmodule 2 in residual (realTypeSourceSubmodule 2),
      coveringDimension (sourceIsospectralSet ENNReal.ofNat_ne_top φ) = ⊤ := by
  filter_upwards [eventually_residual_infinite_source_open_gaps (p := 2) (by simp) (by norm_num)] with φ hφ
  exact sourceHilbertInfiniteGap_coveringDimension_eq_top φ hφ

end NLS.ZakharovShabat
