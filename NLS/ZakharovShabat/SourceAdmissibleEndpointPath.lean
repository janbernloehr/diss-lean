import NLS.ZakharovShabat.SourceCriticalRootCommonEndpointLimit
import NLS.ComplexAnalysis.PiecewiseImproperPathIntegral

/-!
# Admissible endpoint paths in the original isolating disks

Admissibility means precisely that every interior point avoids all
periodic gap segments. On the unchanged source W, the actual quotient
has zero improper integral along every interior C¹ admissible endpoint
path, and along every finite piecewise interior C¹ such path. The
integrals are limits of actual truncated integrals, not primitive values
used as definitions. Absolutely integrable paths retain the ordinary
curve-integral formulation as well.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source's admissibility condition, allowing gaps only at endpoints. -/
def SourceAdmissiblePath (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    {a b : ℂ} (γ : Path a b) : Prop :=
  ∀ t ∈ Ioo (0 : ℝ) 1, γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ

/-- At a corner the path is still interior, so it must also avoid all gaps. -/
def SourceAdmissiblePiecewisePath (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    {a b : ℂ} (Γ : PiecewiseInteriorC1Path a b) : Prop :=
  Γ.PiecesInside (sourceCanonicalRootDomain hp hp1 ψ) ∧
    Γ.VerticesInside (sourceCanonicalRootDomain hp hp1 ψ)

/-- Admissibility is literally avoidance of every indexed gap at interior parameters. -/
theorem sourceAdmissiblePath_iff (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    {a b : ℂ} (γ : Path a b) :
    SourceAdmissiblePath hp hp1 ψ γ ↔
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ m : ℤ, γ.extend t ∉ sourcePeriodicSegment hp hp1 ψ m := Iff.rfl

/-- Continuity of the actual quotient on each original cut disk. -/
theorem SourceIsolatingNeighborhoods.criticalRatio_continuousOn_cutDisk
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    ContinuousOn (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ))
      (D n \ sourcePeriodicSegment hp hp1 ψ n) := by
  apply (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ).continuousOn.mono
  intro z hz m
  by_cases hm : m = n
  · subst m; exact hz.2
  · exact hD.disk_subset_omittedDomain ψ hψ n hz.1 m hm

/-- Every admissible endpoint path has zero improper integral, without
requiring absolute integrability or a half-plane restriction. -/
theorem SourceLemma10_11CircleData.endpointPath_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n))
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1))
    (hadm : SourceAdmissiblePath hp hp1 ψ γ) (hin : range γ ⊆ D n) :
    Tendsto (fun t : ℝ × ℝ => truncatedPathIntegral
      (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) γ t.1 t.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ))) (𝓝 0) ∧
    improperPathIntegral (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) γ = 0 := by
  obtain ⟨F,A,hF,hA,hB⟩ := h.originalDisk_common_endpoint_primitive hD ψ hψW hψV n
  have hγD : ∀ t ∈ Ioo (0 : ℝ) 1, γ.extend t ∈ D n \ sourcePeriodicSegment hp hp1 ψ n := by
    intro t ht
    refine ⟨?_,hadm t ht n⟩
    rw [γ.extend_apply (Ioo_subset_Icc_self ht)]
    exact hin ⟨⟨t,Ioo_subset_Icc_self ht⟩,rfl⟩
  have hlim := tendsto_truncatedPathIntegral_of_primitive_boundary _ F _
    (hD.criticalRatio_continuousOn_cutDisk ψ hψV n) hF γ hγ hγD hA hB
  rw [sub_self] at hlim
  exact ⟨hlim,hlim.limUnder_eq⟩

/-- When the actual path integral is absolutely integrable it is also
zero in the ordinary curve-integral convention. -/
theorem SourceLemma10_11CircleData.endpointPath_curveIntegral_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hadm : SourceAdmissiblePath hp hp1 ψ γ) (hin : range γ ⊆ D n)
    (hint : CurveIntegrable (holomorphicOneForm
      (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ))) γ) :
    (∫ᶜ z in γ, holomorphicOneForm (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) z) = 0 := by
  obtain ⟨F,A,hF,hA,hB⟩ := h.originalDisk_common_endpoint_primitive hD ψ hψW hψV n
  apply curveIntegral_eq_zero_of_primitive_boundary_ends _ F _ hF γ hγ _ hint hA hB
  intro t ht
  refine ⟨?_,hadm t ht n⟩
  rw [γ.extend_apply (Ioo_subset_Icc_self ht)]
  exact hin ⟨⟨t,Ioo_subset_Icc_self ht⟩,rfl⟩

/-- Corners do not alter the endpoint assertion: every finite admissible
piecewise interior C¹ path has zero improper integral on the original disk. -/
theorem SourceLemma10_11CircleData.endpointPiecewisePath_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_11CircleData hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ)
    (Γ : PiecewiseInteriorC1Path
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n))
    (hadm : SourceAdmissiblePiecewisePath hp hp1 ψ Γ)
    (hin : ∀ i u, Γ.edge i u ∈ D n) :
    Tendsto (fun t : ℝ × ℝ => Γ.truncatedIntegral
      (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) t.1 t.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[<] (1 : ℝ))) (𝓝 0) ∧
    Γ.improperIntegral (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0 := by
  obtain ⟨F,A,hF,hA,hB⟩ := h.originalDisk_common_endpoint_primitive hD ψ hψW hψV n
  have hpieces : Γ.PiecesInside (D n \ sourcePeriodicSegment hp hp1 ψ n) := by
    intro i t ht
    refine ⟨?_,hadm.1 i t ht n⟩
    rw [(Γ.edge i).extend_apply (Ioo_subset_Icc_self ht)]
    exact hin i ⟨t,Ioo_subset_Icc_self ht⟩
  have hvertices : Γ.VerticesInside (D n \ sourcePeriodicSegment hp hp1 ψ n) := by
    intro k hk0 hkc
    refine ⟨?_,hadm.2 k hk0 hkc n⟩
    simpa only [Path.source] using hin ⟨k,hkc⟩ 0
  have hlim := Γ.tendsto_truncatedIntegral_eq_zero_of_common_boundary _ F _
    (hD.criticalRatio_continuousOn_cutDisk ψ hψV n) hF hpieces hvertices A hA hB
  exact ⟨hlim,hlim.limUnder_eq⟩

end NLS.ZakharovShabat
