import NLS.ZakharovShabat.SourceAngularEndpointConnector
import NLS.ZakharovShabat.SourceCriticalGapQuotientContinuity

/-!
# Actual endpoint integration data on a common complex source domain

Intersect the proved Lemma 12.12 psi domain with the proved joint
omitted-root domain. Assigned cluster isolation puts every selected
gap inside its omitted-root domain. The resulting open neighborhood
of the entire real locus supplies every hypothesis used by the angular
endpoint bound and singular connector theorems at every complex source.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The three actual spectral properties used to control the selected
endpoint singularity. The scalar estimates are derived from these. -/
structure SourceAngularEndpointSpectralData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) : Prop where
  isOpen_omitted : IsOpen (sourceStandardRootOmittedDomain hp hp1 ψ m)
  gap_avoids_other_gaps : sourcePeriodicSegment hp hp1 ψ m ⊆
    sourceStandardRootOmittedDomain hp hp1 ψ m
  analytic_omitted : AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 m ψ)
    (sourceStandardRootOmittedDomain hp hp1 ψ m)

/-- One open source neighborhood contains all real potentials and
supports the actual Section 12 family and all endpoint integration data.
The original simply connected psi domain and its full estimates are retained. -/
theorem exists_sourceAngularEndpoint_common_domain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          ∀ ψ ∈ W, ∀ m : ℤ, SourceAngularEndpointSpectralData hp hp1 ψ m := by
  obtain ⟨U,W₀,hU,hW₀,hW₀conn,hreal,hW₀U,s,hs⟩ := exists_sourcePsi_lemma12_12 hp hp1
  obtain ⟨V,hV,_,hVreal,hroot⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  let W := W₀ ∩ V
  refine ⟨W₀,W,hW₀,hW₀conn,hreal,hW₀.inter hV,
    fun ψ hψ => ⟨hreal hψ,hVreal hψ⟩,inter_subset_left,s,hs,?_⟩
  intro ψ hψ m
  obtain ⟨O,_,_,hψO,_,φ,N,ε,_,_,hclusters,hsegments,hdisjoint⟩ :=
    hU.2.2.2 ψ (hW₀U hψ.1)
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    (hsegments ψ hψO m).trans
      (sourceIsolatingDisc_subset_omittedDomain hp hp1 φ ψ N ε
        (hclusters ψ hψO) hdisjoint m)
  have hD : IsOpen (sourceStandardRootOmittedDomain hp hp1 ψ m) := by
    have heq : sourceStandardRootOmittedDomain hp hp1 ψ m =
        (fun z : ℂ => (z,ψ)) ⁻¹' sourceStandardRootOmittedJointDomain hp hp1 V m := by
      ext z
      change (∀ k, k ≠ m → z ∉ sourcePeriodicSegment hp hp1 ψ k) ↔
        ψ ∈ V ∧ (∀ k, k ≠ m → z ∉ sourcePeriodicSegment hp hp1 ψ k)
      exact ⟨fun hz => ⟨hψ.2,hz⟩,And.right⟩
    rw [heq]
    exact (hroot m).1.preimage (continuous_id.prodMk continuous_const)
  exact ⟨hD,hseg,sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 m V
    (hroot m).2.1 ψ hψ.2⟩

end NLS.ZakharovShabat
