import NLS.ZakharovShabat.SourceAbelianUniformCollapsedFilling

/-! # Full spectral primitives near the entire real-source locus

An open connected almost-real neighborhood is covered by source balls
on which one infinite disc family works. At every complex source in
each ball, the actual projected exterior primitive extends to the
whole complement of noncollapsed gaps. These existence theorems do
not yet identify all choices across different source balls.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One common root neighborhood and a connected almost-real subdomain
support full spectral continuation at every nearby complex source.
The neighborhoods control all gap indices at once, and collapsed gaps
are analytically filled. -/
theorem exists_sourceAbelian_almostReal_spectral_continuation (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen W ∧ IsOpen V ∧ IsConnected V ∧
      realTypeSourceLocus p ⊆ V ∧ V ⊆ W ∧
      IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W) ∧
      ∀ ψ ∈ V, ∃ D : SourceAbelianUniformDiscFamily hp hp1 W,
        ψ ∈ ball D.source.val D.sourceRadius ∧
        ∀ χ ∈ ball D.source.val D.sourceRadius, ∃ F : ℤ → ℂ → ℂ, ∀ n : ℤ,
          EqOn (F n) (fun z => sourceAbelianProjectedPrimitive hp hp1 n (z,χ)) D.exterior ∧
          AnalyticOnNhd ℂ (F n) (sourceOpenGapComplement hp hp1 χ) ∧
          (∀ z ∈ sourceCanonicalRootDomain hp hp1 χ,
            HasDerivAt (F n) (deriv (canonicalDiscriminant hp (periodOnePotential χ)) z / sourceCanonicalRoot hp hp1 χ z) z) ∧
          ∀ z : ℂ, F n z = F 0 z+I*(Real.pi : ℂ)*n := by
  obtain ⟨W₀,hW₀,_,hreal₀,hD₀,hroot₀⟩ := exists_global_source_analytic_canonicalRoot hp hp1
  obtain ⟨Wc,hWc,hrealc,hfill⟩ := exists_global_sourceAbelian_complexDisc_collapsed_extension hp hp1
  let W := W₀ ∩ Wc
  have hW : IsOpen W := hW₀.inter hWc
  have hrealW : realTypeSourceLocus p ⊆ W := fun ψ hψ => ⟨hreal₀ hψ,hrealc hψ⟩
  have hdeq : sourceCanonicalRootJointDomain hp hp1 W =
      sourceCanonicalRootJointDomain hp hp1 W₀ ∩ (univ ×ˢ Wc) := by
    ext t
    simp only [sourceCanonicalRootJointDomain,W,mem_ofPred_eq,mem_inter_iff,mem_prod,mem_univ,true_and]
    tauto
  have hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W) := by
    rw [hdeq]
    exact hD₀.inter (isOpen_univ.prod hWc)
  have hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W) :=
    hroot₀.mono (fun _ ht => ⟨ht.1.1,ht.2⟩)
  have hlocal (φ : realTypeSourceSubmodule p) := exists_sourceAbelianUniformDiscFamily hp hp1 W hW φ (hrealW φ.property)
  choose D hsource using hlocal
  let U : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, ball (D φ).source.val (D φ).sourceRadius
  have hU : IsOpen U := isOpen_iUnion (fun _ => isOpen_ball)
  have hrealU : realTypeSourceLocus p ⊆ U := by
    intro ψ hψ
    apply mem_iUnion.mpr
    refine ⟨⟨ψ,hψ⟩,?_⟩
    rw [hsource]
    exact mem_ball_self (D ⟨ψ,hψ⟩).sourceRadius_pos
  have hUW : U ⊆ W := by
    intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact (D φ).source_subset hφ
  let V := connectedComponentIn U (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealV : realTypeSourceLocus p ⊆ V :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealU
  have hVU : V ⊆ U := connectedComponentIn_subset U 0
  refine ⟨W,V,hW,hU.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr (hrealU hzero),hrealV,
    hVU.trans hUW,hD,hroot,?_⟩
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hVU hψ)
  refine ⟨D φ,hφ,?_⟩
  intro χ hχ
  apply (D φ).exists_filled_spectral_primitive hD hroot χ hχ
  intro j hj f hf
  obtain ⟨H,hH,heq,_,_⟩ := hfill χ ((D φ).source_subset hχ).2 j hj
    ((D φ).center j) ((D φ).outer j)
    (((D φ).segment_subset χ hχ j).trans (ball_subset_ball ((D φ).inner_lt j).le))
    ((D φ).avoids_other χ hχ j) f hf
  exact ⟨H,hH,heq⟩

end NLS.ZakharovShabat
