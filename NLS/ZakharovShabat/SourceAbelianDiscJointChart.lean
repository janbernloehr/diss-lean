import NLS.ZakharovShabat.SourceAbelianCauchyDifferential
import NLS.ZakharovShabat.SourceAbelianCauchySquare

/-! # Normalized interior charts on real-centered source balls

The source ball stays in one fixed analytic root neighborhood. Its
convexity and the contractive real projection give the paths used to
compare interior charts with each other and with exterior charts.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceAbelianDiscJointChart (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) where
  gap : ℤ
  cauchy : SourceAbelianCauchyChart hp hp1 gap
  source : realTypeSourceSubmodule p
  sourceRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  source_subset : ball source.val sourceRadius ⊆ cauchy.sources ∩ W
  normalized : ∀ ψ ∈ cauchy.sources, cauchy.offset ψ = -I*(Real.pi : ℂ)*gap

/-- Every selected gap at every real source in W has an interior chart,
including when the selected gap is collapsed. -/
theorem exists_sourceAbelianDiscJointChart (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (φ : realTypeSourceSubmodule p) (hφW : φ.val ∈ W) (j : ℤ) :
    ∃ D : SourceAbelianDiscJointChart hp hp1 W, D.source = φ ∧ D.gap = j := by
  obtain ⟨C,hφ,hnorm⟩ := exists_sourceAbelianCauchyChart_normalized hp hp1 φ j
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp ((C.sources_open.inter hW).mem_nhds ⟨hφ,hφW⟩)
  exact ⟨⟨j,C,φ,r,hr,hsub,hnorm⟩,rfl,rfl⟩

namespace SourceAbelianDiscJointChart
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

def domain (D : SourceAbelianDiscJointChart hp hp1 W) : Set (ℂ × CoeffPair p) :=
  (ball D.cauchy.center D.cauchy.radius ×ˢ ball D.source.val D.sourceRadius) ∩ sourceCanonicalRootJointDomain hp hp1 W

def toFun (D : SourceAbelianDiscJointChart hp hp1 W) (n : ℤ) : ℂ × CoeffPair p → ℂ := D.cauchy.primitive n

theorem isOpen_domain (D : SourceAbelianDiscJointChart hp hp1 W)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W)) : IsOpen D.domain :=
  (isOpen_ball.prod isOpen_ball).inter hD

/-- Within the isolating disc, only its own selected cut is excluded. -/
theorem mem_domain_iff (D : SourceAbelianDiscJointChart hp hp1 W) (t : ℂ × CoeffPair p) :
    t ∈ D.domain ↔ t.1 ∈ ball D.cauchy.center D.cauchy.radius ∧
      t.2 ∈ ball D.source.val D.sourceRadius ∧ t.1 ∉ sourcePeriodicSegment hp hp1 t.2 D.gap := by
  constructor
  · intro ht
    exact ⟨ht.1.1,ht.1.2,ht.2.2 D.gap⟩
  · rintro ⟨hz,hψ,hcut⟩
    exact ⟨⟨hz,hψ⟩,(D.source_subset hψ).2,
      sourceAbelian_discComplement_subset_rootDomain hp hp1 t.2 D.gap D.cauchy.center D.cauchy.radius
        (D.cauchy.avoids_other t.2 (D.source_subset hψ).1) ⟨hz,hcut⟩⟩

theorem analytic (D : SourceAbelianDiscJointChart hp hp1 W) (n : ℤ) : AnalyticOnNhd ℂ (D.toFun n) D.domain :=
  (D.cauchy.primitive_analytic n).mono (fun _ ht => ⟨ht.1.1,(D.source_subset ht.1.2).1,ht.2.2 D.gap⟩)

theorem hasFDerivAt (D : SourceAbelianDiscJointChart hp hp1 W)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ D.domain) :
    HasFDerivAt (D.toFun n)
      ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t :=
  D.cauchy.primitive_hasFDerivAt W hD hroot D.normalized n t ht.2 ht.1.1 (D.source_subset ht.1.2).1

theorem exp_toFun (D : SourceAbelianDiscJointChart hp hp1 W)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ D.domain) :
    exp (D.toFun n t) = exp (I*(Real.pi : ℂ)*n)*sourceFloquetJointMultiplier hp hp1 t :=
  D.cauchy.primitive_exp W hD hroot t.2 (D.source_subset ht.1.2).1 ht.2.1
    (D.normalized t.2 (D.source_subset ht.1.2).1) n t.1 ⟨ht.1.1,ht.2.2 D.gap⟩

theorem real_eq (D : SourceAbelianDiscJointChart hp hp1 W) (n : ℤ)
    (φ : realTypeSourceSubmodule p) (z : ℂ) (ht : (z,φ.val) ∈ D.domain) :
    D.toFun n (z,φ.val) = sourceAbelianPrimitive hp hp1 φ.val φ.property z+I*(Real.pi : ℂ)*n :=
  D.cauchy.primitive_eq_real φ (D.source_subset ht.1.2).1 n ⟨ht.1.1,ht.2.2 D.gap⟩

/-- Projection and its entire straight path preserve the source ball.
Spectral cut avoidance is supplied separately by each overlap argument. -/
theorem projectionPath_mem_ball (D : SourceAbelianDiscJointChart hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball D.source.val D.sourceRadius)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
    sourceRealProjectionPath hp ψ s ∈ ball D.source.val D.sourceRadius := by
  have h := sourceSegmentMap_mem (univ : Set ℂ) (ball D.source.val D.sourceRadius)
    (sourceRealTypeProjection hp ψ).val (convex_ball _ _)
    (sourceRealTypeProjection_mem_ball hp D.source D.sourceRadius ψ hψ) (0,ψ) ⟨mem_univ _,hψ⟩ s hs
  simpa only [sourceSegmentMap,Complex.coe_smul,sourceRealProjectionPath] using! h.2

end SourceAbelianDiscJointChart
end NLS.ZakharovShabat
