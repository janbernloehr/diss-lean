import NLS.ZakharovShabat.SourceDistantCriticalGapQuotientAnalyticNeighborhood
import NLS.ZakharovShabat.SourceCriticalGapQuotientUniform

/-! # A common analytic domain for every critical squared-gap quotient

Finite head neighborhoods are combined with the uniform distant-index
neighborhood. The resulting connected almost-real domain supports the
exact squared-gap identity and analytic coefficients even at complex
collapsed gaps. It may be chosen inside any prescribed open real neighborhood.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All indices share one neighborhood of each real source. -/
theorem exists_local_source_allCriticalGapQuotients_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ n : ℤ, AnalyticOnNhd ℂ (fun ψ => sourceCriticalGapQuotient hp hp1 ψ n) V := by
  obtain ⟨K,U,hU,hφU,htail⟩ := exists_local_source_distantCriticalGapQuotient_analytic hp hp1 φ hφ
  have hhead : ∀ᶠ ψ in 𝓝 φ, ∀ n ∈ Finset.Icc (-(K:ℤ)) (K:ℤ),
      AnalyticAt ℂ (fun χ => sourceCriticalGapQuotient hp hp1 χ n) ψ := by
    rw [Finset.eventually_all]
    intro n _
    exact (analyticAt_sourceCriticalGapQuotient_apply_of_realType hp hp1 φ hφ n).eventually_analyticAt
  obtain ⟨V,hVsub,hV,hφV⟩ := _root_.mem_nhds_iff.mp hhead
  refine ⟨U ∩ V,hU.inter hV,⟨hφU,hφV⟩,?_⟩
  intro n ψ hψ
  by_cases hn : n.natAbs ≤ K
  · apply hVsub hψ.2 n
    simp only [Finset.mem_Icc]
    omega
  · exact htail ψ hψ.1 n (by omega)

/-- An almost-real domain carrying the precise identities needed at collapsed gaps. -/
structure SourceCriticalGapAnalyticDomain (hp : p ≠ ⊤) (hp1 : 1 < p) where
  domain : Set (CoeffPair p)
  isOpen : IsOpen domain
  isConnected : IsConnected domain
  real_subset : realTypeSourceLocus p ⊆ domain
  quotient_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ
    (fun ψ => sourceCriticalGapQuotient hp hp1 ψ n) domain
  squaredGap_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ
    (fun ψ => (sourcePeriodicGapDisplacement hp hp1 ψ n)^2) domain
  offset_eq : ∀ ψ ∈ domain, ∀ n : ℤ,
    canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*sourceCriticalGapQuotient hp hp1 ψ n

/-- The domain can be intersected with any earlier prescribed open almost-real domain. -/
theorem exists_sourceCriticalGapAnalyticDomain_within (hp : p ≠ ⊤) (hp1 : 1 < p)
    (U : Set (CoeffPair p)) (hU : IsOpen U) (hrealU : realTypeSourceLocus p ⊆ U) :
    ∃ D : SourceCriticalGapAnalyticDomain hp hp1, D.domain ⊆ U := by
  let A := {ψ : CoeffPair p | ∀ n : ℤ,
    AnalyticAt ℂ (fun χ => sourceCriticalGapQuotient hp hp1 χ n) ψ}
  have hrA : realTypeSourceLocus p ⊆ interior A := by
    intro φ hφ
    obtain ⟨V,hV,hφV,hVdata⟩ := exists_local_source_allCriticalGapQuotients_analytic hp hp1 φ hφ
    exact mem_interior_iff_mem_nhds.mpr
      (mem_of_superset (hV.mem_nhds hφV) (fun ψ hψ n => hVdata n ψ hψ))
  obtain ⟨We,hWe,_,hre,he⟩ := exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
  obtain ⟨Wg,hWg,_,hrg,hg⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  let S := U ∩ (interior A ∩ (We ∩ Wg))
  have hS : IsOpen S := hU.inter (isOpen_interior.inter (hWe.inter hWg))
  have hrS : realTypeSourceLocus p ⊆ S := fun φ hφ => ⟨hrealU hφ,hrA hφ,hre hφ,hrg hφ⟩
  let W := connectedComponentIn S (0 : CoeffPair p)
  have h0 : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hWS : W ⊆ S := connectedComponentIn_subset S 0
  refine ⟨{
    domain := W
    isOpen := hS.connectedComponentIn
    isConnected := isConnected_connectedComponentIn_iff.mpr (hrS h0)
    real_subset := isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn h0 hrS
    quotient_analytic := fun n ψ hψ => interior_subset (hWS hψ).2.1 n
    squaredGap_analytic := fun n ψ hψ => by
      simpa only [sourcePeriodicGapDisplacement_apply] using (hg ψ (hWS hψ).2.2.2 n).2
    offset_eq := fun ψ hψ n => (he ψ (hWS hψ).2.2.1 n).2
  },fun ψ hψ => (hWS hψ).1⟩

/-- Existence without an additional prescribed domain. -/
theorem nonempty_sourceCriticalGapAnalyticDomain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Nonempty (SourceCriticalGapAnalyticDomain hp hp1) := by
  obtain ⟨D,_⟩ := exists_sourceCriticalGapAnalyticDomain_within hp hp1 univ isOpen_univ (subset_univ _)
  exact ⟨D⟩

namespace SourceCriticalGapAnalyticDomain
variable {hp : p ≠ ⊤} {hp1 : 1 < p} (D : SourceCriticalGapAnalyticDomain hp hp1)

/-- Gap magnitudes are continuous even where the lexicographic endpoints switch. -/
theorem continuousAt_gap_norm (φ : CoeffPair p) (hφ : φ ∈ D.domain) (n : ℤ) :
    ContinuousAt (fun ψ => ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖) φ := by
  have h := (D.squaredGap_analytic n φ hφ).continuousAt.norm.sqrt
  simpa only [norm_pow,Real.sqrt_sq (norm_nonneg _)] using h

/-- The squared-gap identity gives analyticity of the actual critical-midpoint offset. -/
theorem analyticAt_offset (φ : CoeffPair p) (hφ : φ ∈ D.domain) (n : ℤ) :
    AnalyticAt ℂ (fun ψ => canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n-canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n) φ := by
  apply ((D.squaredGap_analytic n φ hφ).mul (D.quotient_analytic n φ hφ)).congr
  filter_upwards [D.isOpen.mem_nhds hφ] with ψ hψ
  exact (D.offset_eq ψ hψ n).symm

end SourceCriticalGapAnalyticDomain
end NLS.ZakharovShabat
