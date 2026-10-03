import NLS.ZakharovShabat.SourceAbelianDiscGluing
import NLS.ZakharovShabat.SourceOpenGapComplement

/-! # Neighborhoods of collapsed gaps in the enlarged spectral domain

An isolating disc contains no other cuts. When its selected gap is a
singleton, every point of the punctured disc is in the original cut
complement, and the whole disc is in the open-gap complement.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A collapsed gap is an isolated missing point of the original cut
complement and an interior point of the enlarged domain. -/
theorem exists_sourceCollapsedGap_neighborhood
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    ∃ U : Set ℂ, IsOpen U ∧
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∈ U ∧
      U ⊆ sourceOpenGapComplement hp hp1 φ ∧
      U \ {canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} ⊆
        sourceCanonicalRootDomain hp hp1 φ := by
  obtain ⟨D⟩ := nonempty_sourceAbelianDiscPrimitive hp hp1 φ hφ n
  have hsub : ball D.center D.radius \
      {canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n} ⊆
      sourceCanonicalRootDomain hp hp1 φ := by
    rw [← sourcePeriodicSegment_eq_singleton_of_zeroGap hp hp1 φ n hn]
    exact sourceAbelian_discComplement_subset_rootDomain hp hp1 φ n D.center D.radius D.avoids_other
  refine ⟨ball D.center D.radius,isOpen_ball,D.segment_subset (left_mem_segment ℝ _ _),?_,hsub⟩
  intro z hz
  by_cases he : z = canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  · subst z
    exact sourcePeriodicSegment_subset_openGapComplement_of_zeroGap hp hp1 φ hφ n hn
      (left_mem_segment ℝ _ _)
  · exact sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ (hsub ⟨hz,he⟩)

/-- Near a collapsed endpoint, approaching off all cuts is exactly
approaching in the ordinary punctured plane. -/
theorem nhdsWithin_sourceCanonicalRootDomain_collapsed
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    𝓝[sourceCanonicalRootDomain hp hp1 φ]
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) =
    𝓝[≠] (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) := by
  obtain ⟨U,hU,ha,_,hsub⟩ := exists_sourceCollapsedGap_neighborhood hp hp1 φ hφ n hn
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
  have heq : U ∩ sourceCanonicalRootDomain hp hp1 φ = U \ {a} := by
    ext z
    constructor
    · intro hz
      refine ⟨hz.1,?_⟩
      rintro rfl
      exact hz.2 n (left_mem_segment ℝ _ _)
    · intro hz
      exact ⟨hz.1,hsub hz⟩
  calc
    _ = 𝓝[U ∩ sourceCanonicalRootDomain hp hp1 φ] a :=
      (nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (hU.mem_nhds ha))).symm
    _ = 𝓝[U ∩ {a}ᶜ] a := by rw [heq]; rfl
    _ = _ := nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (hU.mem_nhds ha))

/-- Removing only the noncollapsed cuts gives an open set for every
real source, without a finite-gap assumption. -/
theorem isOpen_sourceOpenGapComplement_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) : IsOpen (sourceOpenGapComplement hp hp1 φ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  rcases mem_sourceOpenGapComplement_cases hp hp1 φ z hz with hroot | ⟨n,hn,hseg⟩
  · exact Filter.mem_of_superset
      ((isOpen_sourceCanonicalRootDomain_of_realType hp hp1 φ hφ).mem_nhds hroot)
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ)
  · rw [sourcePeriodicSegment_eq_singleton_of_zeroGap hp hp1 φ n hn] at hseg
    rcases hseg with rfl
    obtain ⟨U,hU,ha,hsub,_⟩ := exists_sourceCollapsedGap_neighborhood hp hp1 φ hφ n hn
    exact Filter.mem_of_superset (hU.mem_nhds ha) hsub

end NLS.ZakharovShabat
