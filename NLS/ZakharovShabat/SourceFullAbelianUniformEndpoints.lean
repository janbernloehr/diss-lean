import NLS.ZakharovShabat.SourceFullAbelianUniformNormalization

/-! # Exact endpoint limits on one almost-real source neighborhood

Local cut-disc limits give limits on the whole complement of noncollapsed
gaps. At a collapsed endpoint the filled function itself has the prescribed
value. The common source balls cover an open connected neighborhood of the
whole real-source locus, with every gap controlled on each ball.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem endpoint_mem_ball (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (a : ℂ) (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j} : Set ℂ)) :
    a ∈ ball (C.discs.center j) (C.discs.outer j) := by
  rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with rfl | rfl
  · exact C.segment_subset_outer j ψ hψ (left_mem_segment ℝ _ _)
  · exact C.segment_subset_outer j ψ hψ (right_mem_segment ℝ _ _)

theorem ball_subset_openGapComplement_of_collapsed (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (j : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j = 0) :
    ball (C.discs.center j) (C.discs.outer j) ⊆ sourceOpenGapComplement hp hp1 ψ := by
  intro z hz k hk
  have hkj : k ≠ j := by rintro rfl; exact hk hgap
  exact C.discs.avoids_other ψ hψ j (ball_subset_closedBall hz) k hkj

/-- The endpoint limit is relative to the complete filled spectral
domain, with no restriction to an individual disc or approach direction. -/
theorem fullPrimitive_endpoint_limit_openGap (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (j n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (a : ℂ) (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j} : Set ℂ)) :
    Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,ψ))
      (𝓝[sourceOpenGapComplement hp hp1 ψ] a) (𝓝 (I*(Real.pi : ℂ)*(n-j))) := by
  have haB := C.endpoint_mem_ball j ψ hψ a ha
  have hlim := C.fullPrimitive_endpoint_limit j n ψ hψ a ha
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j = 0
  · obtain ⟨E⟩ := C.charts ψ hψ
    have hac := (sourceFullAbelianPrimitive_spectral_analytic E n a
      (C.ball_subset_openGapComplement_of_collapsed j ψ hψ hgap haB)).continuousAt
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j
    let U := ball (C.discs.center j) (C.discs.outer j) \ sourcePeriodicSegment hp hp1 ψ j
    let : NeBot (𝓝[U] a) := mem_closure_iff_nhdsWithin_neBot.mp
      ((dense_complex_segment_complement l r).open_subset_closure_inter isOpen_ball haB)
    have he := tendsto_nhds_unique (hac.tendsto.mono_left (nhdsWithin_le_nhds (s := U))) hlim
    simpa only [he] using hac.tendsto.mono_left (nhdsWithin_le_nhds (s := sourceOpenGapComplement hp hp1 ψ))
  · have heq : ball (C.discs.center j) (C.discs.outer j) ∩ sourceOpenGapComplement hp hp1 ψ =
        ball (C.discs.center j) (C.discs.outer j) \ sourcePeriodicSegment hp hp1 ψ j := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1,hz.2 j hgap⟩
      · intro hz
        exact ⟨hz.1,sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ
          (sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ j _ _ (C.discs.avoids_other ψ hψ j) hz)⟩
    have hf := nhdsWithin_inter_of_mem
      (mem_nhdsWithin_of_mem_nhds (t := sourceOpenGapComplement hp hp1 ψ) (isOpen_ball.mem_nhds haB))
    rw [heq] at hf
    rw [hf] at hlim
    exact hlim

/-- At a collapsed endpoint the already-filled canonical function has
its exact normalized value, not only a limiting value. -/
theorem fullPrimitive_collapsed_endpoint_value (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (j n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j = 0)
    (a : ℂ) (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j} : Set ℂ)) :
    sourceFullAbelianPrimitive hp hp1 W n (a,ψ) = I*(Real.pi : ℂ)*(n-j) := by
  have haOpen := C.ball_subset_openGapComplement_of_collapsed j ψ hψ hgap (C.endpoint_mem_ball j ψ hψ a ha)
  let : NeBot (𝓝[sourceOpenGapComplement hp hp1 ψ] a) := mem_closure_iff_nhdsWithin_neBot.mp (subset_closure haOpen)
  obtain ⟨E⟩ := C.charts ψ hψ
  exact tendsto_nhds_unique
    ((sourceFullAbelianPrimitive_spectral_analytic E n a haOpen).continuousAt.continuousWithinAt.tendsto)
    (C.fullPrimitive_endpoint_limit_openGap j n ψ hψ a ha)

end SourceFullAbelianUniformCauchyFamily

/-- One open connected almost-real source neighborhood has exact
endpoint limits for every gap. Each complex base point has one source
radius working simultaneously for all gaps and all normalization indices. -/
theorem exists_sourceFullAbelian_almostReal_uniformEndpoints (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ realTypeSourceLocus p ⊆ V ∧ V ⊆ W ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (sourceFullAbelianPrimitive hp hp1 W n)
        (sourceCanonicalRootJointDomain hp hp1 V)) ∧
      ∀ ψ ∈ V, ∃ r : ℝ, 0 < r ∧ ball ψ r ⊆ V ∧
        ∀ χ ∈ ball ψ r, Nonempty (SourceAbelianSpectralChart hp hp1 W χ) ∧
          ∀ (j n : ℤ) (a : ℂ),
            a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) j,
              canonicalPeriodicRight hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) j} : Set ℂ) →
            Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,χ))
              (𝓝[sourceOpenGapComplement hp hp1 χ] a) (𝓝 (I*(Real.pi : ℂ)*(n-j))) := by
  obtain ⟨W,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  choose C hC using hfamilies
  let U : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, ball (C φ).discs.source.val (C φ).discs.sourceRadius
  have hU : IsOpen U := isOpen_iUnion (fun _ => isOpen_ball)
  have hrealU : realTypeSourceLocus p ⊆ U := by
    intro ψ hψ
    apply mem_iUnion.mpr
    refine ⟨⟨ψ,hψ⟩,?_⟩
    rw [hC]
    exact mem_ball_self (C ⟨ψ,hψ⟩).discs.sourceRadius_pos
  have hUW : U ⊆ W := by
    intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact (C φ).discs.source_subset hφ
  let V := connectedComponentIn U (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealV : realTypeSourceLocus p ⊆ V :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealU
  have hVU : V ⊆ U := connectedComponentIn_subset U 0
  have hV : IsOpen V := hU.connectedComponentIn
  refine ⟨W,V,hV,isConnected_connectedComponentIn_iff.mpr (hrealU hzero),hrealV,hVU.trans hUW,?_,?_⟩
  · intro n t ht
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hVU ht.1)
    exact (C φ).full_analytic n t ⟨hφ,ht.2⟩
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hVU hψ)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp ((hV.inter isOpen_ball).mem_nhds ⟨hψ,hφ⟩)
  refine ⟨r,hr,fun χ hχ => (hsub hχ).1,?_⟩
  intro χ hχ
  exact ⟨(C φ).charts χ (hsub hχ).2,fun j n a ha => (C φ).fullPrimitive_endpoint_limit_openGap j n χ (hsub hχ).2 a ha⟩

end NLS.ZakharovShabat
