import NLS.ZakharovShabat.SourceAbelianComplexDomainConnected

/-! # Independence of the full complex spectral continuation

Two constructions share a nonempty open exterior region. Their
analytic primitives therefore agree on the connected cut complement,
and density identifies their fillings at every collapsed gap as well.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianUniformDiscFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}

/-- The same exterior normalization determines the full spectral
function independently of both the source ball and the root neighborhood. -/
theorem spectral_primitives_eq (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (E : SourceAbelianUniformDiscFamily hp hp1 V)
    (ψ : CoeffPair p) (hψD : ψ ∈ ball D.source.val D.sourceRadius)
    (hψE : ψ ∈ ball E.source.val E.sourceRadius) (n : ℤ) (F G : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F (sourceOpenGapComplement hp hp1 ψ))
    (hG : AnalyticOnNhd ℂ G (sourceOpenGapComplement hp hp1 ψ))
    (hFE : EqOn F (fun z => sourceAbelianProjectedPrimitive hp hp1 n (z,ψ)) D.exterior)
    (hGE : EqOn G (fun z => sourceAbelianProjectedPrimitive hp hp1 n (z,ψ)) E.exterior) :
    EqOn F G (sourceOpenGapComplement hp hp1 ψ) := by
  have hsub := sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ
  obtain ⟨a,haD,haE⟩ := D.exterior_inter_nonempty E
  have haroot : a ∈ sourceCanonicalRootDomain hp hp1 ψ := by
    rw [D.rootDomain_eq_union ψ hψD]
    exact Or.inl haD
  have hfg : F =ᶠ[𝓝 a] G := by
    filter_upwards [(D.isOpen_exterior.inter E.isOpen_exterior).mem_nhds ⟨haD,haE⟩] with z hz
    exact (hFE hz.1).trans (hGE hz.2).symm
  have heq := (hF.mono hsub).eqOn_of_preconnected_of_eventuallyEq (hG.mono hsub)
    (D.isConnected_rootDomain ψ hψD).isPreconnected haroot hfg
  apply continuous_eqOn_of_dense_on_open (sourceCanonicalRootDomain hp hp1 ψ) _
    (dense_sourceCanonicalRootDomain_complex hp hp1 ψ) (E.isOpen_openGapComplement ψ hψE)
    _ _ hF.continuousOn hG.continuousOn
  intro z hz
  exact heq hz.2

end NLS.ZakharovShabat.SourceAbelianUniformDiscFamily
