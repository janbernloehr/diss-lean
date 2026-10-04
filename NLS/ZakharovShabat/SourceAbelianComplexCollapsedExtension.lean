import NLS.ZakharovShabat.SourceAbelianComplexEndpointLimits

/-! # Removing collapsed cuts from complex-source abelian primitives

The deleted critical-root quotient is analytic through a collapsed gap.
A primitive of it on the full disc differs from any existing cut-disc
primitive by one constant, which can be restored without changing any
cut-disc values. This gives analytic removal and full endpoint limits.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An analytic extension of the derivative fills the cut disc without
 changing a single value of the original primitive. -/
theorem exists_sourceAbelian_complexDisc_extension_of_derivative_extension
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j : ℤ) (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ j ⊆ ball c R)
    (F g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (ball c R))
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j,
      HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z)
    (heq : EqOn g (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z) (ball c R \ sourcePeriodicSegment hp hp1 ψ j)) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball c R) ∧
      EqOn H F (ball c R \ sourcePeriodicSegment hp hp1 ψ j) ∧
      (∀ z ∈ ball c R, HasDerivAt H (g z) z) ∧
      ∀ a ∈ ball c R, Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ j] a) (𝓝 (H a)) := by
  obtain ⟨G,hG⟩ := exists_primitive_on_convex g (ball c R) (convex_ball c R) isOpen_ball hg.differentiableOn
  obtain ⟨C,hC⟩ := (isOpen_sourceAbelian_complexDisc hp hp1 ψ j c R).exists_eq_add_of_deriv_eq
    (isConnected_sourceAbelian_complexDisc hp hp1 ψ j c R hseg).isPreconnected
    (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hG z hz.1).differentiableAt.differentiableWithinAt)
    (fun z hz => (hF z hz).deriv.trans ((heq hz).symm.trans (hG z hz.1).deriv.symm))
  have hH (z : ℂ) (hz : z ∈ ball c R) : HasDerivAt (fun w => G w+C) (g z) z := (hG z hz).add_const C
  refine ⟨fun z => G z+C,
    (show DifferentiableOn ℂ (fun z => G z+C) (ball c R) from
      fun z hz => (hH z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball,
    fun z hz => (hC hz).symm,hH,?_⟩
  intro a ha
  apply ((hH a ha).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hC hz).symm

/-- One almost-real source neighborhood supports analytic removal at
 every collapsed gap, for every primitive with the actual derivative. -/
theorem exists_global_sourceAbelian_complexDisc_collapsed_extension
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ j : ℤ, sourcePeriodicGapDisplacement hp hp1 ψ j = 0 →
        ∀ (c : ℂ) (R : ℝ), sourcePeriodicSegment hp hp1 ψ j ⊆ ball c R →
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ j →
          ∀ F : ℂ → ℂ, (∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j,
            HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z) →
          ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball c R) ∧
            EqOn H F (ball c R \ sourcePeriodicSegment hp hp1 ψ j) ∧
            (∀ z ∈ ball c R, HasDerivAt H (sourceCriticalRootRatioExtension hp hp1 j ψ z) z) ∧
            ∀ a ∈ ball c R, Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ j] a) (𝓝 (H a)) := by
  obtain ⟨W,hW,hreal,hdata⟩ := exists_global_sourceCriticalRootRatio_analytic_of_zeroGap hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro ψ hψ j hgap c R hseg hother F hF
  have hroot := sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ j c R hother
  apply exists_sourceAbelian_complexDisc_extension_of_derivative_extension hp hp1 ψ j c R hseg F
    (sourceCriticalRootRatioExtension hp hp1 j ψ)
    ((hdata ψ hψ j hgap).1.mono (ball_subset_closedBall.trans hother)) hF
  intro z hz
  exact (hdata ψ hψ j hgap).2 z (hroot hz)

/-- A single source neighborhood gives full finite endpoint limits for
 all complex cut-disc primitives, whether the selected gap is open or collapsed. -/
theorem exists_global_sourceAbelian_complexDisc_endpoint_limits
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ (j : ℤ) (c : ℂ) (R : ℝ),
        sourcePeriodicSegment hp hp1 ψ j ⊆ ball c R →
        closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ j →
        ∀ F : ℂ → ℂ, (∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j,
          HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z) →
        ∃ A B : ℂ,
          Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ j]
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)) (𝓝 A) ∧
          Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ j]
            (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)) (𝓝 B) := by
  obtain ⟨W₁,hW₁,hreal₁,hE⟩ := exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  obtain ⟨W₂,hW₂,hreal₂,hfill⟩ := exists_global_sourceAbelian_complexDisc_collapsed_extension hp hp1
  refine ⟨W₁ ∩ W₂,hW₁.inter hW₂,fun ψ hψ => ⟨hreal₁ hψ,hreal₂ hψ⟩,?_⟩
  intro ψ hψ j c R hseg hother F hF
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ j = 0
  · obtain ⟨H,_,_,_,hlim⟩ := hfill ψ hψ.2 j hgap c R hseg hother F hF
    exact ⟨_,_,hlim _ (hseg (left_mem_segment ℝ _ _)),hlim _ (hseg (right_mem_segment ℝ _ _))⟩
  · exact exists_sourceAbelian_complexDisc_endpoint_limits hp hp1 ψ j c R hseg hother (hE ψ hψ.1 j) hgap F hF

/-- The actual normalized joint primitive continues into a full moving
complex cut disc, has finite limits at both endpoints, and extends
analytically across every collapsed gap. The fixed collar, disc, and
source neighborhood work for every normalization index. -/
theorem exists_local_sourceAbelian_complexDisc_continuation_with_limits
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (j : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
      ∃ (c : ℂ) (r R : ℝ), 0 < r ∧ r < R ∧
        ∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ j ⊆ ball c r ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ j ∧
          ∀ n : ℤ, ∃ F : ℂ → ℂ,
            EqOn F (fun z => sourceAbelianJointPrimitive hp hp1 n (z,ψ)) (ball c R \ closedBall c r) ∧
            AnalyticOnNhd ℂ F (ball c R \ sourcePeriodicSegment hp hp1 ψ j) ∧
            (∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j,
              HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
                sourceCanonicalRoot hp hp1 ψ z) z) ∧
            (∃ A B : ℂ,
              Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ j]
                (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)) (𝓝 A) ∧
              Tendsto F (𝓝[ball c R \ sourcePeriodicSegment hp hp1 ψ j]
                (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)) (𝓝 B)) ∧
            (sourcePeriodicGapDisplacement hp hp1 ψ j = 0 →
              ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball c R) ∧ EqOn H F (ball c R \ sourcePeriodicSegment hp hp1 ψ j)) := by
  obtain ⟨V₀,hV₀,hφV₀,c,r,R,hr,hrR,hcont⟩ := exists_local_sourceAbelian_complexDisc_continuation hp hp1 φ j
  obtain ⟨W₁,hW₁,hreal₁,hlim⟩ := exists_global_sourceAbelian_complexDisc_endpoint_limits hp hp1
  obtain ⟨W₂,hW₂,hreal₂,hfill⟩ := exists_global_sourceAbelian_complexDisc_collapsed_extension hp hp1
  refine ⟨V₀ ∩ (W₁ ∩ W₂),hV₀.inter (hW₁.inter hW₂),
    ⟨hφV₀,hreal₁ φ.property,hreal₂ φ.property⟩,c,r,R,hr,hrR,?_⟩
  intro ψ hψ
  obtain ⟨hseg,hother,_,hF⟩ := hcont ψ hψ.1
  have hsegR := hseg.trans (ball_subset_ball hrR.le)
  refine ⟨hseg,hother,?_⟩
  intro n
  obtain ⟨F,heq,hana,hder⟩ := hF n
  refine ⟨F,heq,hana,hder,hlim ψ hψ.2.1 j c R hsegR hother F hder,?_⟩
  intro hgap
  obtain ⟨H,hH,hHF,_,_⟩ := hfill ψ hψ.2.2 j hgap c R hsegR hother F hder
  exact ⟨H,hH,hHF⟩

end NLS.ZakharovShabat
