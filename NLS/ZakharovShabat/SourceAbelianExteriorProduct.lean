import NLS.ZakharovShabat.SourceAbelianRadialCompatibility

/-! # A common abelian source neighborhood over the full spectral exterior

All-index isolation keeps every straight source path off all spectral
cuts outside one fixed isolating-disc family. The radial continuation
therefore supplies one source ball over the entire unbounded exterior,
including its boundary, with all normalizations and the full joint
differential at once.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One common complex-source ball works over the full unbounded
exterior of a fixed family of pairwise disjoint isolating discs. -/
theorem exists_sourceAbelianRadial_exterior_product
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) :
    ∃ (W : Set (CoeffPair p)) (N : ℕ) (ε r : ℝ),
      IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W) ∧
      0 < ε ∧ ε ≤ Real.pi/4 ∧ 0 < r ∧
      (∀ i j : ℤ, i ≠ j → Disjoint (sourceIsolatingDisc hp hp1 φ.val N ε i) (sourceIsolatingDisc hp hp1 φ.val N ε j)) ∧
      (∀ ψ ∈ Metric.ball φ.val r, ∀ n : ℤ,
        sourceSpectralCluster hp hp1 ψ n ⊆ sourceIsolatingDisc hp hp1 φ.val N ε n) ∧
      ((⋃ n : ℤ, sourceIsolatingDisc hp hp1 φ.val N ε n)ᶜ ×ˢ Metric.ball φ.val r) ⊆
        sourceAbelianRadialDomain hp hp1 φ W := by
  obtain ⟨W,hW,_,hreal,hD,hroot⟩ := exists_global_source_analytic_canonicalRoot hp hp1
  obtain ⟨N,ε,hε,hεmax,V,hV,_,hφV,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ.val φ.property
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp ((hW.inter hV).mem_nhds ⟨hreal φ.property,hφV⟩)
  have hφr : φ.val ∈ Metric.ball φ.val r := Metric.mem_ball_self hr
  have hrootExt (z : ℂ) (hz : z ∈ (⋃ n : ℤ, sourceIsolatingDisc hp hp1 φ.val N ε n)ᶜ)
      (ψ : CoeffPair p) (hψ : ψ ∈ Metric.ball φ.val r) :
      (z,ψ) ∈ sourceCanonicalRootJointDomain hp hp1 W := by
    refine ⟨(hrV hψ).1,?_⟩
    intro n hn
    apply hz
    exact mem_iUnion.mpr ⟨n,sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val ψ N ε n
      (hcluster ψ (hrV hψ).2 n) hn⟩
  refine ⟨W,N,ε,r,hD,hroot,hε,hεmax,hr,hdisjoint,fun ψ hψ => hcluster ψ (hrV hψ).2,?_⟩
  intro t ht s hs
  have hpath := sourceSegmentMap_mem ((⋃ n : ℤ, sourceIsolatingDisc hp hp1 φ.val N ε n)ᶜ)
    (Metric.ball φ.val r) φ.val (convex_ball _ _) hφr t ht s hs
  exact hrootExt _ hpath.1 _ hpath.2

/-- The exterior continuation is jointly analytic for all signed
indices, has the exact joint differential at complex sources, and
matches the actual normalized integral at every nearby real source. -/
theorem exists_sourceAbelianRadial_uniform_exterior
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) :
    ∃ (N : ℕ) (ε r : ℝ), 0 < ε ∧ ε ≤ Real.pi/4 ∧ 0 < r ∧
      (∀ i j : ℤ, i ≠ j → Disjoint (sourceIsolatingDisc hp hp1 φ.val N ε i) (sourceIsolatingDisc hp hp1 φ.val N ε j)) ∧
      (∀ ψ ∈ Metric.ball φ.val r, ∀ m : ℤ,
        sourceSpectralCluster hp hp1 ψ m ⊆ sourceIsolatingDisc hp hp1 φ.val N ε m) ∧
      ∀ n : ℤ,
        AnalyticOnNhd ℂ (sourceAbelianRadialPrimitive hp hp1 φ n)
          ((⋃ m : ℤ, sourceIsolatingDisc hp hp1 φ.val N ε m)ᶜ ×ˢ Metric.ball φ.val r) ∧
        (∀ t ∈ ((⋃ m : ℤ, sourceIsolatingDisc hp hp1 φ.val N ε m)ᶜ ×ˢ Metric.ball φ.val r),
          HasFDerivAt (sourceAbelianRadialPrimitive hp hp1 φ n)
            ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
              fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t) ∧
        (∀ t ∈ ((⋃ m : ℤ, sourceIsolatingDisc hp hp1 φ.val N ε m)ᶜ ×ˢ Metric.ball φ.val r),
          t ∈ sourceAbelianJointDomain hp hp1 →
            sourceAbelianRadialPrimitive hp hp1 φ n t = sourceAbelianJointPrimitive hp hp1 n t) ∧
        ∀ (ψ : realTypeSourceSubmodule p), ψ.val ∈ Metric.ball φ.val r →
          ∀ z ∈ (⋃ m : ℤ, sourceIsolatingDisc hp hp1 φ.val N ε m)ᶜ,
            sourceAbelianRadialPrimitive hp hp1 φ n (z,ψ.val) =
              sourceAbelianPrimitive hp hp1 ψ.val ψ.property z+I*(Real.pi : ℂ)*n := by
  obtain ⟨W,N,ε,r,hD,hroot,hε,hεmax,hr,hdisjoint,hcluster,hsub⟩ :=
    exists_sourceAbelianRadial_exterior_product hp hp1 φ
  have hM := sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot
  refine ⟨N,ε,r,hε,hεmax,hr,hdisjoint,hcluster,?_⟩
  intro n
  refine ⟨(sourceAbelianRadialPrimitive_analytic hp hp1 φ W hD hM n).mono hsub,
    fun t ht => sourceAbelianRadialPrimitive_hasFDerivAt hp hp1 φ W hD hroot n t (hsub ht),?_,?_⟩
  · intro t ht hjoint
    exact sourceAbelianRadialPrimitive_eq_joint hp hp1 φ W hD hM r hr t.1
      (fun χ hχ => hsub ⟨ht.1,hχ⟩) t.2 ht.2 hjoint n
  · intro ψ hψ z hz
    exact sourceAbelianRadialPrimitive_eq_real_on_convex hp hp1 φ W (Metric.ball φ.val r)
      hD hM (convex_ball _ _) (Metric.mem_ball_self hr) z (fun χ hχ => hsub ⟨hz,hχ⟩) n ψ hψ

end NLS.ZakharovShabat
