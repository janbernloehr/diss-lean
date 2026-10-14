import NLS.ZakharovShabat.SourceCriticalRootRatioCommonDomain

/-!
# Equation (2.15) with its original common domains

The literal full product, its -i normalization, absolute factor convergence
and spectral and joint analyticity all hold on the same source domain as
Lemma 10.10. The fixed local neighborhoods and closed disks are retained.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equation (2.15) and the analytic-domain assertions immediately following it. -/
structure SourceEquation2_15Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceLemma10_10Data hp hp1 W
  absolute : ∀ ψ : CoeffPair p, ∀ z : ℂ,
    Summable (fun m : ℤ => ‖(canonicalCriticalPoints hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/sourceStandardRoot hp hp1 ψ m z-1‖)
  product : ∀ ψ : CoeffPair p, ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
    HasProd (fun m : ℤ => (canonicalCriticalPoints hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/sourceStandardRoot hp hp1 ψ m z)
      (Complex.I*sourceCriticalRootRatioJoint hp hp1 (z,ψ))
  normalization : ∀ ψ : CoeffPair p, ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z/sourceCanonicalRoot hp hp1 ψ z =
      -Complex.I*(∏' m : ℤ, (canonicalCriticalPoints hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/sourceStandardRoot hp hp1 ψ m z)
  spectral : ∀ ψ ∈ W,
    AnalyticOnNhd ℂ (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ))
      (⋃ m : ℤ, sourcePeriodicSegment hp hp1 ψ m)ᶜ
  joint : IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
    AnalyticOnNhd ℂ (sourceCriticalRootRatioJoint hp hp1) (sourceCanonicalRootJointDomain hp hp1 W)
  literal_joint : AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => ∏' m : ℤ,
    (canonicalCriticalPoints hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) m-t.1)/
      sourceStandardRoot hp hp1 t.2 m t.1) (sourceCanonicalRootJointDomain hp hp1 W)
  neighborhoods : ∀ φ ∈ W,
    ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ D c, SourceCanonicalRootNeighborhoods hp hp1 V D c ∧
        AnalyticOnNhd ℂ (sourceCriticalRootRatioJoint hp hp1) ((⋃ m : ℤ, closure (D m))ᶜ ×ˢ V) ∧
        AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => ∏' m : ℤ,
          (canonicalCriticalPoints hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) m-t.1)/
            sourceStandardRoot hp hp1 t.2 m t.1) ((⋃ m : ℤ, closure (D m))ᶜ ×ˢ V)

/-- The product representation strengthens the retained common domain without shrinking it. -/
theorem SourceLemma10_10Data.criticalRootProduct
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)} (h : SourceLemma10_10Data hp hp1 W) :
    SourceEquation2_15Data hp hp1 W := by
  have h7 := h.previous.previous
  refine ⟨h,summable_norm_sourceCriticalRootRatio_factor_sub_one hp hp1,
    sourceCriticalRootRatio_hasProd hp hp1,sourceCriticalRootRatio_product hp hp1,
    h7.criticalRatioSpectral,⟨h7.joint.1,h7.criticalRatioJoint⟩,h7.criticalRatioLiteralJoint,?_⟩
  intro φ hφ
  obtain ⟨V,ho,hc,hφV,hVW,D,c,hD⟩ := h7.neighborhoods φ hφ
  exact ⟨V,ho,hc,hφV,hVW,D,c,hD,
    h7.criticalRatioClosedFixed hVW hD.toSourceIsolatingNeighborhoods,
    h7.criticalRatioLiteralClosedFixed hVW hD.toSourceIsolatingNeighborhoods⟩

/-- Equation (2.15) for every finite p>1, retaining all preceding common-domain conclusions. -/
theorem sourceEquation2_15 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceEquation2_15Data hp hp1 W := by
  obtain ⟨W,ho,hc,hr,h⟩ := sourceLemma10_10 hp hp1
  exact ⟨W,ho,hc,hr,h.criticalRootProduct⟩

end NLS.ZakharovShabat
