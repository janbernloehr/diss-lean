import NLS.ZakharovShabat.SourceAbelianEnlargedPrimitive

/-! # Uniform exterior products in one enlarged analytic domain

One analytic root neighborhood works for every real-source anchor.
Projection preserves its real-centered source balls, so the common
projected domain contains every corresponding full spectral-exterior
product. A connected open neighborhood of the real locus then supplies
uniform exterior products also at complex base potentials.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A prescribed open source neighborhood admits a uniform exterior
product in the projection-normalized domain around each real source. -/
theorem exists_sourceAbelianProjected_exterior_product_in
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (W : Set (CoeffPair p))
    (hW : IsOpen W) (hφW : φ.val ∈ W) :
    ∃ (N : ℕ) (ε r : ℝ), 0 < ε ∧ ε ≤ Real.pi/4 ∧ 0 < r ∧ Metric.ball φ.val r ⊆ W ∧
      (∀ i j : ℤ, i ≠ j → Disjoint (sourceIsolatingDisc hp hp1 φ.val N ε i) (sourceIsolatingDisc hp hp1 φ.val N ε j)) ∧
      (∀ ψ ∈ Metric.ball φ.val r, ∀ n : ℤ,
        sourceSpectralCluster hp hp1 ψ n ⊆ sourceIsolatingDisc hp hp1 φ.val N ε n) ∧
      ((⋃ n : ℤ, sourceIsolatingDisc hp hp1 φ.val N ε n)ᶜ ×ˢ Metric.ball φ.val r) ⊆
        sourceAbelianProjectedDomain hp hp1 W := by
  obtain ⟨N,ε,hε,hεmax,V,hV,_,hφV,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ.val φ.property
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp ((hW.inter hV).mem_nhds ⟨hφW,hφV⟩)
  have hrootExt (z : ℂ) (hz : z ∈ (⋃ n : ℤ, sourceIsolatingDisc hp hp1 φ.val N ε n)ᶜ)
      (ψ : CoeffPair p) (hψ : ψ ∈ Metric.ball φ.val r) :
      (z,ψ) ∈ sourceCanonicalRootJointDomain hp hp1 W := by
    refine ⟨(hrV hψ).1,?_⟩
    intro n hn
    exact hz (mem_iUnion.mpr ⟨n,sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val ψ N ε n
      (hcluster ψ (hrV hψ).2 n) hn⟩)
  refine ⟨N,ε,r,hε,hεmax,hr,fun ψ hψ => (hrV hψ).1,hdisjoint,
    fun ψ hψ => hcluster ψ (hrV hψ).2,?_⟩
  intro t ht s hs
  have hproj := sourceRealTypeProjection_mem_ball hp φ r t.2 ht.2
  have hpath := sourceSegmentMap_mem ((⋃ n : ℤ, sourceIsolatingDisc hp hp1 φ.val N ε n)ᶜ)
    (Metric.ball φ.val r) (sourceRealTypeProjection hp t.2).val (convex_ball _ _) hproj t ht s hs
  exact hrootExt _ hpath.1 _ hpath.2

/-- A single enlarged joint function works around every complex source
in one open connected neighborhood of the entire real-source locus.
Its full unbounded exterior products have one common source radius,
valid for all signed spectral indices and all normalized primitives. -/
theorem exists_sourceAbelianEnlarged_almostReal_exterior
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ realTypeSourceLocus p ⊆ V ∧ V ⊆ W ∧
      IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W) ∧
      ∀ ψ ∈ V, ∃ (φ : realTypeSourceSubmodule p) (N : ℕ) (ε r : ℝ),
        0 < ε ∧ ε ≤ Real.pi/4 ∧ 0 < r ∧ Metric.ball ψ r ⊆ V ∧
        (∀ i j : ℤ, i ≠ j → Disjoint (sourceIsolatingDisc hp hp1 φ.val N ε i) (sourceIsolatingDisc hp hp1 φ.val N ε j)) ∧
        (∀ χ ∈ Metric.ball ψ r, ∀ n : ℤ,
          sourceSpectralCluster hp hp1 χ n ⊆ sourceIsolatingDisc hp hp1 φ.val N ε n) ∧
        ((⋃ n : ℤ, sourceIsolatingDisc hp hp1 φ.val N ε n)ᶜ ×ˢ Metric.ball ψ r) ⊆
          sourceAbelianEnlargedDomain hp hp1 W := by
  obtain ⟨W,hW,_,hreal,hD,hroot⟩ := exists_global_source_analytic_canonicalRoot hp hp1
  have hloc (φ : realTypeSourceSubmodule p) := exists_sourceAbelianProjected_exterior_product_in hp hp1 φ W hW (hreal φ.property)
  choose N ε r hε hεmax hr hballW hdisjoint hcluster hprod using hloc
  let U : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, Metric.ball φ.val (r φ)
  have hU : IsOpen U := isOpen_iUnion (fun _ => Metric.isOpen_ball)
  have hrealU : realTypeSourceLocus p ⊆ U := by
    intro φ hφ
    exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,Metric.mem_ball_self (hr ⟨φ,hφ⟩)⟩
  have hUW : U ⊆ W := by
    intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact hballW φ hφ
  let V := connectedComponentIn U (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealV : realTypeSourceLocus p ⊆ V :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealU
  have hVU : V ⊆ U := connectedComponentIn_subset U 0
  have hV : IsOpen V := hU.connectedComponentIn
  refine ⟨W,V,hV,isConnected_connectedComponentIn_iff.mpr (hrealU hzero),hrealV,hVU.trans hUW,hD,hroot,?_⟩
  intro ψ hψ
  obtain ⟨φ,hφψ⟩ := mem_iUnion.mp (hVU hψ)
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp ((hV.inter Metric.isOpen_ball).mem_nhds ⟨hψ,hφψ⟩)
  refine ⟨φ,N φ,ε φ,δ,hε φ,hεmax φ,hδ,fun χ hχ => (hδsub hχ).1,hdisjoint φ,
    fun χ hχ => hcluster φ χ (hδsub hχ).2,?_⟩
  intro t ht
  exact Or.inr (hprod φ ⟨ht.1,(hδsub ht.2).2⟩)

end NLS.ZakharovShabat
