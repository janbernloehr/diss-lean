import NLS.FunctionalAnalysis.CircleProductCubeEmbedding
import NLS.FunctionalAnalysis.CoveringDimensionConnected
import NLS.ZakharovShabat.SourceHilbertInfiniteGapTopology

/-! # Covering-dimension reductions for actual isospectral sets

Actual infinite-gap Hilbert isospectral sets contain closed copies of every
finite cube. Their finite covering-dimension bounds would therefore bound
all cubes. The numerical cube lower-bound theorem remains an explicit
premise in the reduction to infinite covering dimension. Independently,
one open gap already obstructs covering dimension zero.
-/
noncomputable section
open Set Topology NLS.FunctionalAnalysis
open scoped unitInterval
namespace NLS.ZakharovShabat

/-- An actual infinite-gap isospectral set contains closed cubes of every finite dimension. -/
theorem sourceHilbertInfiniteGap_exists_closedEmbedding_cube
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∉ sourceFiniteGapLocus (by simp) (by norm_num)) (m : ℕ) :
    ∃ f : (Fin m → unitInterval) → sourceIsospectralSet ENNReal.ofNat_ne_top φ,
      IsClosedEmbedding f := by
  let := sourceHilbertOpenGapIndex_infinite_of_not_finiteGap φ hφ
  obtain ⟨e⟩ := sourceHilbertIsospectralSet_homeomorphic_circles φ
  obtain ⟨f,hf⟩ := exists_closedEmbedding_cube_circleProduct
    (ι := sourceHilbertOpenGapIndex φ) m
  exact ⟨e.symm ∘ f,e.symm.isClosedEmbedding.comp hf⟩

/-- A finite covering-dimension bound on the actual infinite-gap set bounds every cube. -/
theorem sourceHilbertInfiniteGap_coveringDimensionLE_cube
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∉ sourceFiniteGapLocus (by simp) (by norm_num)) {n : ℕ}
    (h : HasCoveringDimensionLE (sourceIsospectralSet ENNReal.ofNat_ne_top φ) n) (m : ℕ) :
    HasCoveringDimensionLE (Fin m → unitInterval) n := by
  obtain ⟨f,hf⟩ := sourceHilbertInfiniteGap_exists_closedEmbedding_cube φ hφ m
  exact h.of_isClosedEmbedding hf

/-- The numerical cube lower bound is the remaining premise for each infinite-gap dimension bound. -/
theorem sourceHilbertInfiniteGap_not_coveringDimensionLE_of_cube
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∉ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℕ)
    (hcube : ¬ HasCoveringDimensionLE (Fin (n+1) → unitInterval) n) :
    ¬ HasCoveringDimensionLE (sourceIsospectralSet ENNReal.ofNat_ne_top φ) n :=
  fun h => hcube (sourceHilbertInfiniteGap_coveringDimensionLE_cube φ hφ h (n+1))

/-- One actual open gap already excludes covering dimension zero. -/
theorem sourceHilbertIsospectralSet_not_coveringDimensionLE_zero
    (φ : realTypeSourceSubmodule 2) (hφ : Nonempty (sourceHilbertOpenGapIndex φ)) :
    ¬ HasCoveringDimensionLE (sourceIsospectralSet ENNReal.ofNat_ne_top φ) 0 := by
  let := hφ
  have hi : Function.Injective (fun x : unitInterval => Circle.exp x) := by
    intro x y h
    apply Subtype.ext
    exact Circle.exp_injOn_Icc (by linarith [Real.two_le_pi] : (1 : ℝ)-0 < 2*Real.pi)
      x.property y.property h
  let : Nontrivial Circle := hi.nontrivial
  obtain ⟨e⟩ := sourceHilbertIsospectralSet_homeomorphic_circles φ
  intro h
  exact not_hasCoveringDimensionLE_zero_of_preconnected (h.homeomorph e)

end NLS.ZakharovShabat
