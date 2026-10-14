import NLS.ZakharovShabat.SourceBoundarySimpleNeighborhood
import NLS.ZakharovShabat.SourceDistantCriticalPointsAnalyticNeighborhood
import Mathlib.Topology.Connected.LocallyConnected

/-!
# One almost-real domain for the simple spectral coordinates

The paragraph preceding Lemma 10.2 concerns every ordinary boundary root
and every discriminant critical root, with no central-index exclusions.
Finite central analyticity neighborhoods combine with a common tail
neighborhood. Taking the connected component of an open intersection
retains the entire connected real-type locus and any prescribed earlier
almost-real domain constraints.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Analyticity and simplicity of every ordinary boundary and critical coordinate. -/
structure SourceSimpleSpectralDomainData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) : Prop where
  boundary : ∀ ψ ∈ W, ∀ b : BoundaryCondition, ∀ n : ℤ,
    AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b χ n) ψ ∧
    deriv (periodOneBoundaryCharacteristic hp hp1 b ψ) (canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) ≠ 0
  critical : ∀ ψ ∈ W, ∀ n : ℤ,
    AnalyticAt ℂ (fun χ : CoeffPair p =>
      canonicalCriticalPoints hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ ∧
    deriv (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) ≠ 0

/-- Central and tail critical coordinates are simple and analytic on one source neighborhood. -/
theorem exists_local_source_allCriticalPoints_simple_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ ∀ ψ ∈ U, ∀ n : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p =>
        canonicalCriticalPoints hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ ∧
      deriv (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
        (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) ≠ 0 := by
  obtain ⟨N,T,hT,hφT,htail⟩ := exists_local_source_distantCanonicalCriticalPoints_analytic hp hp1 φ hφ
  obtain ⟨S,hS,hφS,hsimple⟩ := exists_local_source_allCanonicalCriticalPoints_simple hp hp1 φ hφ
  have hhead : ∀ᶠ ψ in 𝓝 φ, ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      AnalyticAt ℂ (fun χ : CoeffPair p =>
        canonicalCriticalPoints hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ := by
    rw [Finset.eventually_all]
    intro n _
    exact (analyticAt_sourceCanonicalCriticalPoint_of_realType hp hp1 n φ hφ).eventually_analyticAt
  obtain ⟨H,hHsub,hH,hφH⟩ := _root_.mem_nhds_iff.mp hhead
  refine ⟨T ∩ (H ∩ S),hT.inter (hH.inter hS),⟨hφT,hφH,hφS⟩,?_⟩
  intro ψ hψ n
  refine ⟨?_,hsimple ψ hψ.2.2 n⟩
  by_cases hn : n.natAbs ≤ N
  · exact hHsub hψ.2.1 n (by simp only [Finset.mem_Icc]; omega)
  · exact htail ψ hψ.1 n (by omega)

/-- The simple analytic coordinates share a connected almost-real domain inside any prescribed one. -/
theorem exists_sourceSimpleSpectralDomain_within
    (hp : p ≠ ⊤) (hp1 : 1 < p) (U : Set (CoeffPair p))
    (hU : IsOpen U) (hrealU : realTypeSourceLocus p ⊆ U) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      W ⊆ U ∧ SourceSimpleSpectralDomainData hp hp1 W := by
  obtain ⟨B,hB,hrealB,hboundary⟩ := exists_sourceBoundaryRoots_simple_common_domain hp hp1
  let A : Set (CoeffPair p) := {ψ | ∀ n : ℤ,
    AnalyticAt ℂ (fun χ : CoeffPair p =>
      canonicalCriticalPoints hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ ∧
    deriv (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) ≠ 0}
  have hrealA : realTypeSourceLocus p ⊆ interior A := by
    intro φ hφ
    obtain ⟨V,hV,hφV,h⟩ := exists_local_source_allCriticalPoints_simple_analytic hp hp1 φ hφ
    exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hV.mem_nhds hφV) h)
  let S := U ∩ (B ∩ interior A)
  have hS : IsOpen S := hU.inter (hB.inter isOpen_interior)
  have hrealS : realTypeSourceLocus p ⊆ S := fun φ hφ => ⟨hrealU hφ,hrealB hφ,hrealA hφ⟩
  let W := connectedComponentIn S (0 : CoeffPair p)
  have h0 : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hWS : W ⊆ S := connectedComponentIn_subset S 0
  refine ⟨W,hS.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr (hrealS h0),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn h0 hrealS,
    fun ψ hψ => (hWS hψ).1,?_,?_⟩
  · intro ψ hψ b n
    exact hboundary ψ (hWS hψ).2.1 b n
  · intro ψ hψ n
    exact interior_subset (hWS hψ).2.2 n

/-- Simplicity refers to the original boundary operator's algebraic multiplicity. -/
theorem SourceSimpleSpectralDomainData.boundary_multiplicity
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceSimpleSpectralDomainData hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (b : BoundaryCondition) (n : ℤ) :
    b.algebraicMultiplicity hp (periodOneBoundaryPotential hp hp1 ψ).val
      (periodOneBoundaryPotential hp hp1 ψ).property (canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) = 1 := by
  have ha := analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 b ψ
    (canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) (mem_univ _)
  have ho := ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 b ψ n) (h.boundary ψ hψ b n).2
  rw [analyticOrderAt_periodOneBoundaryCharacteristic] at ho
  exact_mod_cast ho

/-- Every canonical critical coordinate has analytic order one as a zero of the derivative. -/
theorem SourceSimpleSpectralDomainData.critical_order
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceSimpleSpectralDomainData hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    analyticOrderAt (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1 := by
  have ha := analyticOnNhd_discriminant_derivative hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ)
    (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) (mem_univ _)
  exact ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (canonicalCriticalPoints_is_critical hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (h.critical ψ hψ n).2

end NLS.ZakharovShabat
