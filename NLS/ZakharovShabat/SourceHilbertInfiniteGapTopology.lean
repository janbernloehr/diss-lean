import NLS.FunctionalAnalysis.InfiniteCircleProductLocalTopology
import NLS.FunctionalAnalysis.ChartedContractibleNeighborhood
import NLS.ZakharovShabat.SourceHilbertFiniteGapManifold
import NLS.ZakharovShabat.SourceGenericGapApproximation

/-! # Local topology of actual infinite-gap isospectral sets

The established homeomorphism to the product of one circle per actual open
gap transfers a local noncontractibility obstruction to the original Hilbert
isospectral set. Such a set admits real normed charts only when the number
of open gaps is finite. This is a manifold obstruction, not a computation
of a covering-dimension invariant.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat

/-- Infinitely many actual open gaps make the circle-factor index type infinite. -/
theorem sourceHilbertOpenGapIndex_infinite_of_not_finiteGap
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∉ sourceFiniteGapLocus (by simp) (by norm_num)) :
    Infinite (sourceHilbertOpenGapIndex φ) := by
  apply Set.infinite_coe_iff.mpr
  change {n : ℤ | canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0}.Infinite at hφ
  simpa only [sourcePeriodicGapDisplacement_apply] using! hφ

/-- In the actual infinite-gap isospectral set, no neighborhood of any point is contractible. -/
theorem sourceHilbertInfiniteGap_not_contractible_neighborhood
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∉ sourceFiniteGapLocus (by simp) (by norm_num))
    (ψ : sourceIsospectralSet ENNReal.ofNat_ne_top φ)
    {V : Set (sourceIsospectralSet ENNReal.ofNat_ne_top φ)} (hV : V ∈ 𝓝 ψ) :
    ¬ ContractibleSpace V := by
  let := sourceHilbertOpenGapIndex_infinite_of_not_finiteGap φ hφ
  obtain ⟨e⟩ := sourceHilbertIsospectralSet_homeomorphic_circles φ
  exact FunctionalAnalysis.not_contractible_neighborhood_of_homeomorph_circleProduct e ψ hV

/-- An actual infinite-gap isospectral set admits no atlas modeled on a real normed vector space. -/
theorem sourceHilbertInfiniteGap_not_chartedSpace
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∉ sourceFiniteGapLocus (by simp) (by norm_num))
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ¬ Nonempty (ChartedSpace E (sourceIsospectralSet ENNReal.ofNat_ne_top φ)) := by
  rintro ⟨h⟩
  let := h
  obtain ⟨e⟩ := sourceHilbertIsospectralSet_homeomorphic_circles φ
  let ψ := e.symm (fun _ => 1)
  obtain ⟨V,hV,hC⟩ := FunctionalAnalysis.exists_contractible_neighborhood_of_chartedSpace
    E (sourceIsospectralSet ENNReal.ofNat_ne_top φ) ψ
  exact sourceHilbertInfiniteGap_not_contractible_neighborhood φ hφ ψ hV hC

/-- Actual Hilbert isospectral sets admit finite-dimensional Euclidean atlases exactly
when their sources have finitely many open periodic gaps. -/
theorem sourceHilbertIsospectralSet_finiteDimensional_charts_iff_finiteGap
    (φ : realTypeSourceSubmodule 2) :
    (∃ N : ℕ, Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin N))
      (sourceIsospectralSet ENNReal.ofNat_ne_top φ))) ↔
        φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
  constructor
  · rintro ⟨N,hN⟩
    by_contra hφ
    exact sourceHilbertInfiniteGap_not_chartedSpace φ hφ _ hN
  · intro hφ
    exact ⟨Nat.card (sourceHilbertOpenGapIndex φ),⟨sourceHilbertFiniteGapChartedSpace φ hφ⟩⟩

/-- Generically the actual Hilbert isospectral set has no finite-dimensional Euclidean atlas. -/
theorem eventually_residual_sourceHilbertIsospectralSet_no_finiteDimensional_charts :
    ∀ᶠ φ : realTypeSourceSubmodule 2 in residual (realTypeSourceSubmodule 2),
      ¬ ∃ N : ℕ, Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin N))
        (sourceIsospectralSet ENNReal.ofNat_ne_top φ)) := by
  filter_upwards [eventually_residual_infinite_source_open_gaps (p := 2)
    (by simp) (by norm_num)] with φ hφ
  intro h
  exact hφ ((sourceHilbertIsospectralSet_finiteDimensional_charts_iff_finiteGap φ).mp h)

end NLS.ZakharovShabat
