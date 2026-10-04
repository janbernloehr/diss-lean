import NLS.ZakharovShabat.SourceAbelianCauchyChart

/-! # Exact complex endpoint constants from real-source uniqueness

The additive discrepancy between the collar primitive and its Cauchy
normalization is analytic in the source. Its actual real-source value
is minus i times the selected index times pi. Uniqueness from the real
form fixes this same constant on a complex neighborhood, including at
collapsed real gaps.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAbelianCauchyChart
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {j : ℤ}

/-- Actual real-source endpoint limits determine the Cauchy offset
 without any choice of logarithm branch or endpoint value. -/
theorem offset_eq_of_real (D : SourceAbelianCauchyChart hp hp1 j) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ D.sources) : D.offset φ.val = -I*(Real.pi : ℂ)*j := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j
  let U := ball D.center D.radius \ sourcePeriodicSegment hp hp1 φ.val j
  let F := sourceAbelianPrimitive hp hp1 φ.val φ.property
  let K : ℂ → ℂ := fun z => sourceAbelianCauchyPrimitive hp hp1 j D.center D.radius (z,φ.val)
  have hl : l ∈ ball D.center D.radius := D.segment_subset_outer φ.val hφ (left_mem_segment ℝ _ _)
  have hroot : U ⊆ sourceCanonicalRootDomain hp hp1 φ.val :=
    sourceAbelian_discComplement_subset_rootDomain hp hp1 φ.val j D.center D.radius (D.avoids_other φ.val hφ)
  let : NeBot (𝓝[U] l) := mem_closure_iff_nhdsWithin_neBot.mp
    ((dense_complex_segment_complement l r).open_subset_closure_inter isOpen_ball hl)
  have hFlim : Tendsto F (𝓝[U] l) (𝓝 (-I*(Real.pi : ℂ)*j)) :=
    (sourceAbelianPrimitive_endpoint_limit hp hp1 φ.val φ.property j l (by simp [l])).mono_left
      (nhdsWithin_mono _ (hroot.trans (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val)))
  have hKlim : Tendsto K (𝓝[U] l) (𝓝 0) :=
    sourceAbelianCauchyPrimitive_endpoint_limit hp hp1 φ.val j D.center D.radius (D.segment_subset_outer φ.val hφ)
      (D.quotient_slice_analytic φ.val hφ) l (by simp [l])
  have heq := primitives_eq_of_common_boundary_limit _ F (fun z => K z-I*(Real.pi : ℂ)*j) U l (-I*(Real.pi : ℂ)*j)
    (isOpen_sourceAbelian_complexDisc hp hp1 φ.val j D.center D.radius)
    (isConnected_sourceAbelian_complexDisc hp hp1 φ.val j D.center D.radius (D.segment_subset_outer φ.val hφ)).isPreconnected
    (fun z hz => sourceAbelianPrimitive_hasDerivAt_quotient hp hp1 φ.val φ.property z (hroot hz))
    (fun z hz => (D.primitive_hasDerivAt φ.val hφ z hz).sub_const _) hFlim
    (by simpa only [zero_sub,neg_mul] using hKlim.sub_const (I*(Real.pi : ℂ)*j))
  have ha : D.anchor ∈ U := ⟨D.anchor_mem.1,D.anchor_off_segment φ.val hφ⟩
  have hval := heq ha
  unfold offset
  rw [sourceAbelianJointPrimitive_eq_real hp hp1 0 φ D.anchor (hroot ha)]
  simp only [Int.cast_zero,mul_zero,add_zero]
  change F D.anchor-K D.anchor = -I*(Real.pi : ℂ)*j
  linear_combination hval

/-- The same offset holds for complex sources near every real point
 of a Cauchy chart, including a real source with a collapsed selected gap. -/
theorem offset_eventually_eq (D : SourceAbelianCauchyChart hp hp1 j) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ D.sources) : ∀ᶠ ψ in 𝓝 φ.val, D.offset ψ = -I*(Real.pi : ℂ)*j := by
  have hlocal := DifferentiableOn.eventually_eq_zero_of_real_form
    (realTypeSourceLocus p) φ.val φ.property
    (by intro x y hx hy; change IsRealType (CoeffPair.toMax p (x+y)); rw [map_add]; exact hx.add hy)
    (by intro t x hx; change IsRealType (CoeffPair.toMax p ((t:ℂ) • x)); rw [map_smul]; exact hx.ofReal_smul t)
    sourceRealPart sourceImagPart sourceRealPart_realType sourceImagPart_realType
    (fun v => (sourceRealPart_add_I_smul_sourceImagPart v).symm) (norm_sourceRealPart_le hp) (norm_sourceImagPart_le hp)
    D.sources D.sources_open hφ (fun ψ => D.offset ψ+I*(Real.pi : ℂ)*j)
    (fun ψ hψ => ((D.offset_analytic ψ hψ).add analyticAt_const).differentiableAt.differentiableWithinAt)
    (by
      intro ψ hψ hreal
      rw [D.offset_eq_of_real ⟨ψ,hreal⟩ hψ]
      ring)
  filter_upwards [hlocal] with ψ hψ
  linear_combination hψ

end SourceAbelianCauchyChart

/-- Every real source and selected gap have a uniform complex chart
 on which the actual endpoint constant has its exact prescribed value. -/
theorem exists_sourceAbelianCauchyChart_normalized
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (j : ℤ) :
    ∃ D : SourceAbelianCauchyChart hp hp1 j, φ.val ∈ D.sources ∧
      ∀ ψ ∈ D.sources, D.offset ψ = -I*(Real.pi : ℂ)*j := by
  obtain ⟨D,hφ⟩ := exists_sourceAbelianCauchyChart hp hp1 φ j
  obtain ⟨U,hUsub,hU,hφU⟩ := _root_.mem_nhds_iff.mp (D.offset_eventually_eq φ hφ)
  refine ⟨D.restrict (D.sources ∩ U) (D.sources_open.inter hU) inter_subset_left,⟨hφ,hφU⟩,?_⟩
  intro ψ hψ
  exact hUsub hψ.2

end NLS.ZakharovShabat
