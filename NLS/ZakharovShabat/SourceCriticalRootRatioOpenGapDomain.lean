import NLS.ZakharovShabat.SourceCriticalRootRatioRegularizedProduct

/-!
# Analyticity across all collapsed gaps on the unchanged common domain

The open-gap complement is covered by the original cut complement and
the omitted domains of collapsed indices. On each member of this open
cover the single continued product equals an already analytic function.
No real-source, finite-gap, small-gap or large-index restriction is used.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The enlarged domain is literally the complement of the union of noncollapsed gaps. -/
theorem sourceOpenGapComplement_eq_compl_iUnion (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    sourceOpenGapComplement hp hp1 ψ =
      (⋃ m : ℤ, ⋃ (_ : canonicalPeriodicGap hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠ 0), sourcePeriodicSegment hp hp1 ψ m)ᶜ := by
  ext z
  simp [sourceOpenGapComplement]

namespace SourceEquation2_15Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The original spectral cut complement is open at each source in the common domain. -/
theorem isOpen_rootDomain (h : SourceEquation2_15Data hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) : IsOpen (sourceCanonicalRootDomain hp hp1 ψ) := by
  have he : (fun z : ℂ => (z,ψ)) ⁻¹' sourceCanonicalRootJointDomain hp hp1 W =
      sourceCanonicalRootDomain hp hp1 ψ := by
    ext z
    change (ψ ∈ W ∧ z ∈ sourceCanonicalRootDomain hp hp1 ψ) ↔ z ∈ sourceCanonicalRootDomain hp hp1 ψ
    exact ⟨And.right,fun hz => ⟨hψ,hz⟩⟩
  rw [← he]
  exact h.joint.1.preimage (continuous_id.prodMk continuous_const)

/-- Each omitted spectral domain is open for the same source, without shrinking W. -/
theorem isOpen_omittedDomain (h : SourceEquation2_15Data hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) : IsOpen (sourceStandardRootOmittedDomain hp hp1 ψ n) := by
  have he : (fun z : ℂ => (z,ψ)) ⁻¹' sourceStandardRootOmittedJointDomain hp hp1 W n =
      sourceStandardRootOmittedDomain hp hp1 ψ n := by
    ext z
    change (ψ ∈ W ∧ z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) ↔
      z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n
    exact ⟨And.right,fun hz => ⟨hψ,hz⟩⟩
  rw [← he]
  exact (h.previous.previous.previous.previous.roots.joint n).1.preimage
    (continuous_id.prodMk continuous_const)

/-- All collapsed gaps are covered simultaneously by their omitted domains. -/
theorem openGapComplement_eq_union (h : SourceEquation2_15Data hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    sourceOpenGapComplement hp hp1 ψ = sourceCanonicalRootDomain hp hp1 ψ ∪
      ⋃ n : ℤ, ⋃ (_ : canonicalPeriodicGap hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0),
        sourceStandardRootOmittedDomain hp hp1 ψ n := by
  obtain ⟨V,_,_,hψV,_,D,c,hD,_,_⟩ := h.neighborhoods ψ hψ
  ext z
  constructor
  · intro hz
    rcases mem_sourceOpenGapComplement_cases hp hp1 ψ z hz with hz | ⟨n,hg,hz⟩
    · exact Or.inl hz
    · exact Or.inr (mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨hg,
        hD.toSourceIsolatingNeighborhoods.disk_subset_omittedDomain ψ hψV n (hD.gap ψ hψV n hz)⟩⟩)
  · rintro (hz | hz)
    · exact sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hz
    · obtain ⟨n,hn⟩ := mem_iUnion.mp hz
      obtain ⟨hg,hz⟩ := mem_iUnion.mp hn
      intro m hm
      by_cases hmn : m = n
      · subst m
        exact (hm hg).elim
      · exact hz m hmn

/-- Removing only noncollapsed gaps gives an open spectral domain, even for complex sources. -/
theorem isOpen_openGapComplement (h : SourceEquation2_15Data hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) : IsOpen (sourceOpenGapComplement hp hp1 ψ) := by
  rw [h.openGapComplement_eq_union ψ hψ]
  exact (h.isOpen_rootDomain ψ hψ).union (isOpen_iUnion (fun n =>
    isOpen_iUnion (fun _ => h.isOpen_omittedDomain ψ hψ n)))

/-- The continued product is analytic throughout the omitted domain of a collapsed index. -/
theorem continued_analytic_omittedDomain (h : SourceEquation2_15Data hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    AnalyticOnNhd ℂ (sourceCriticalRootRatioContinued hp hp1 ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ n) := by
  intro z hz
  apply (h.previous.previous.previous.previous.criticalRatioExtension ψ hψ n z hz).congr
  filter_upwards [(h.isOpen_omittedDomain ψ hψ n).mem_nhds hz] with w hw
  exact (h.continued_eq_extension ψ hψ n hg w hw).symm

/-- One actual function extends analytically across every collapsed gap at once. -/
theorem continued_analytic_openGapComplement (h : SourceEquation2_15Data hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    AnalyticOnNhd ℂ (sourceCriticalRootRatioContinued hp hp1 ψ) (sourceOpenGapComplement hp hp1 ψ) := by
  intro z hz
  rw [h.openGapComplement_eq_union ψ hψ] at hz
  rcases hz with hz | hz
  · have ha := (h.joint.2 (z,ψ) ⟨hψ,hz⟩).comp
      (f := fun z : ℂ => (z,ψ)) (analyticAt_id.prod analyticAt_const)
    apply ha.congr
    filter_upwards [(h.isOpen_rootDomain ψ hψ).mem_nhds hz] with w hw
    exact (h.continued_eq_quotient ψ hψ w hw).symm
  · obtain ⟨n,hn⟩ := mem_iUnion.mp hz
    obtain ⟨hg,hz⟩ := mem_iUnion.mp hn
    exact h.continued_analytic_omittedDomain ψ hψ n hg z hz

end SourceEquation2_15Data
end NLS.ZakharovShabat
