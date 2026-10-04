import NLS.ZakharovShabat.SourceAbelianDiscPrimitive
import NLS.ZakharovShabat.SourceAbelianEnlargedPrimitive
import NLS.ComplexAnalysis.ComplexSegmentComplementConnected

/-! # Continuing the normalized abelian integral into complex cut discs

A compact collar around a selected real gap lies in the existing joint
domain for nearby complex sources. Radial continuation of its actual
primitive fills the whole disc minus the moving complex segment and
retains every collar value, hence the prescribed normalization.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The selected cut disc is connected even when the gap collapses. -/
theorem isConnected_sourceAbelian_complexDisc
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j : ℤ) (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ j ⊆ ball c R) :
    IsConnected (ball c R \ sourcePeriodicSegment hp hp1 ψ j) :=
  (isPathConnected_convex_complex_segment_complement_including_singleton (ball c R) _ _
    isOpen_ball (convex_ball c R) (hseg (left_mem_segment ℝ _ _))).isConnected

theorem isOpen_sourceAbelian_complexDisc
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j : ℤ) (c : ℂ) (R : ℝ) :
    IsOpen (ball c R \ sourcePeriodicSegment hp hp1 ψ j) := by
  apply isOpen_ball.sdiff
  apply IsCompact.isClosed
  change IsCompact (segment ℝ _ _)
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

/-- An actual annular primitive continues throughout the selected cut
 disc, with exactly the same annular values, for a complex potential. -/
theorem exists_sourceAbelian_complexDisc_from_annulus
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j : ℤ) (c : ℂ) (r R : ℝ)
    (hr : 0 ≤ r) (hrR : r < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ j ⊆ ball c r)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ j)
    (G : ℂ → ℂ) (hG : ∀ z ∈ ball c R \ closedBall c r,
      HasDerivAt G (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z) z) :
    ∃ F : ℂ → ℂ, EqOn F G (ball c R \ closedBall c r) ∧
      AnalyticOnNhd ℂ F (ball c R \ sourcePeriodicSegment hp hp1 ψ j) ∧
      ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j,
        HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z) z := by
  have hclosed : IsClosed (sourcePeriodicSegment hp hp1 ψ j) := by
    apply IsCompact.isClosed
    change IsCompact (segment ℝ _ _)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ j
  have hana := (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ).mono
    (sourceAbelian_discComplement_subset_rootDomain hp hp1 ψ j c R hother)
  obtain ⟨F,heq,hF⟩ := exists_primitive_on_disc_complement_of_annular_primitive _ G c
    (sourceStandardRootMidpoint hp hp1 ψ j) r R hr hrR _ hclosed hmid
    ((convex_segment _ _).starConvex hmid) hseg hana hG
  exact ⟨F,heq,(show DifferentiableOn ℂ F (ball c R \ sourcePeriodicSegment hp hp1 ψ j) from
    fun z hz => (hF z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
      (isOpen_sourceAbelian_complexDisc hp hp1 ψ j c R),hF⟩

/-- Equal derivatives and one common value fix the continuation on
 the entire complex cut disc, including a collapsed cut. -/
theorem sourceAbelian_complexDisc_unique
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j : ℤ) (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ j ⊆ ball c R)
    (F G : ℂ → ℂ)
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j,
      HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z)
    (hG : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j,
      HasDerivAt G (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z)
    (a : ℂ) (ha : a ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j) (he : F a = G a) :
    EqOn F G (ball c R \ sourcePeriodicSegment hp hp1 ψ j) := by
  obtain ⟨C,hC⟩ := (isOpen_sourceAbelian_complexDisc hp hp1 ψ j c R).exists_eq_add_of_deriv_eq
    (isConnected_sourceAbelian_complexDisc hp hp1 ψ j c R hseg).isPreconnected
    (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hG z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hF z hz).deriv.trans (hG z hz).deriv.symm)
  have hzero : C = 0 := by have h := hC ha; rw [he] at h; linear_combination -h
  intro z hz
  simpa only [hzero,add_zero] using hC hz

/-- Around every real source and selected gap, one fixed collar and
 disc work for nearby complex sources. Every normalized joint primitive
 continues into the whole moving cut disc, preserving all collar values.
 No open-gap assumption is imposed on the real source or its perturbation. -/
theorem exists_local_sourceAbelian_complexDisc_continuation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (j : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
      ∃ (c : ℂ) (r R : ℝ), 0 < r ∧ r < R ∧
        ∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ j ⊆ ball c r ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ j ∧
          (∀ z ∈ closedBall c R \ ball c r, (z,ψ) ∈ sourceAbelianJointDomain hp hp1) ∧
          ∀ n : ℤ, ∃ F : ℂ → ℂ,
            EqOn F (fun z => sourceAbelianJointPrimitive hp hp1 n (z,ψ)) (ball c R \ closedBall c r) ∧
            AnalyticOnNhd ℂ F (ball c R \ sourcePeriodicSegment hp hp1 ψ j) ∧
            ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j,
              HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
                sourceCanonicalRoot hp hp1 ψ z) z := by
  obtain ⟨V₀,hV₀,hφV₀,c,T,_,hgeom⟩ :=
    exists_local_sourceCriticalRootRatio_uniformEnclosingCircle hp hp1 φ.val φ.property j
  obtain ⟨r,R,hr,hrR,hRT,hsegr⟩ :=
    exists_nested_radii_of_segment_subset_ball _ _ c T (hgeom φ.val hφV₀).1
  let K := closedBall c R \ ball c r
  have hK : IsCompact K := (isCompact_closedBall c R).inter_right isOpen_ball.isClosed_compl
  have hKroot : K ⊆ sourceCanonicalRootDomain hp hp1 φ.val := by
    intro z hz k
    by_cases hk : k = j
    · subst k; exact fun hs => hz.2 (hsegr hs)
    · exact ((hgeom φ.val hφV₀).2.1 ((closedBall_subset_closedBall hRT.le) hz.1)) k hk
  obtain ⟨U,δ,_,hKU,hδ,hprod⟩ := exists_sourceAbelianJointDomain_compact_product hp hp1 φ K hK hKroot
  have hL := (continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ.val φ.property j).eventually
    (isOpen_ball.mem_nhds (hsegr (left_mem_segment ℝ _ _)))
  have hR := (continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ.val φ.property j).eventually
    (isOpen_ball.mem_nhds (hsegr (right_mem_segment ℝ _ _)))
  have hnear : ∀ᶠ ψ in 𝓝 φ.val, ψ ∈ V₀ ∧ ψ ∈ ball φ.val δ ∧ sourcePeriodicSegment hp hp1 ψ j ⊆ ball c r := by
    filter_upwards [hV₀.mem_nhds hφV₀,ball_mem_nhds φ.val hδ,hL,hR] with ψ hψ hψδ hl hr'
    exact ⟨hψ,hψδ,(convex_ball c r).segment_subset hl hr'⟩
  obtain ⟨V,hVsub,hV,hφV⟩ := _root_.mem_nhds_iff.mp hnear
  refine ⟨V,hV,hφV,c,r,R,hr,hrR,?_⟩
  intro ψ hψ
  obtain ⟨hψV₀,hψδ,hseg⟩ := hVsub hψ
  have hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ j :=
    (closedBall_subset_closedBall hRT.le).trans (hgeom ψ hψV₀).2.1
  have hcollar (z : ℂ) (hz : z ∈ K) : (z,ψ) ∈ sourceAbelianJointDomain hp hp1 := by
    simpa only using! hprod (show (z,ψ) ∈ U ×ˢ ball φ.val δ from ⟨hKU hz,hψδ⟩)
  refine ⟨hseg,hother,hcollar,?_⟩
  intro n
  apply exists_sourceAbelian_complexDisc_from_annulus hp hp1 ψ j c r R hr.le hrR hseg hother
    (fun z => sourceAbelianJointPrimitive hp hp1 n (z,ψ))
  intro z hz
  have ht := hcollar z ⟨ball_subset_closedBall hz.1,fun h => hz.2 (ball_subset_closedBall h)⟩
  have hd : HasDerivAt (fun w : ℂ => sourceAbelianJointPrimitive hp hp1 n (w,ψ))
      (deriv (fun w : ℂ => sourceAbelianJointPrimitive hp hp1 n (w,ψ)) z) z := by
    simpa only using! ((sourceAbelianJointPrimitive_analytic hp hp1 n (z,ψ) ht).comp
      (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const)).differentiableAt.hasDerivAt
  rw [sourceAbelianJointPrimitive_spectral_deriv hp hp1 n z ψ ht] at hd
  exact hd

/-- The continuation preserves the enlarged primitive on every collar
 whose joint points lie in the original domain. -/
theorem sourceAbelian_complexDisc_eq_enlarged_on_collar
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (ψ : CoeffPair p) (n : ℤ) (c : ℂ) (r R : ℝ) (F : ℂ → ℂ)
    (hcollar : ∀ z ∈ ball c R \ closedBall c r, (z,ψ) ∈ sourceAbelianJointDomain hp hp1)
    (hF : EqOn F (fun z => sourceAbelianJointPrimitive hp hp1 n (z,ψ)) (ball c R \ closedBall c r)) :
    EqOn F (fun z => sourceAbelianEnlargedPrimitive hp hp1 W n (z,ψ)) (ball c R \ closedBall c r) := by
  intro z hz
  exact (hF hz).trans (sourceAbelianEnlargedPrimitive_eq_joint hp hp1 W hD hM n (hcollar z hz)).symm

/-- A value fixed by the actual real-source normalization propagates
 throughout the entire cut disc. -/
theorem sourceAbelian_complexDisc_eq_real
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (j n : ℤ) (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 φ.val j ⊆ ball c R)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ.val j)
    (F : ℂ → ℂ) (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 φ.val j,
      HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential φ.val)) z / sourceCanonicalRoot hp hp1 φ.val z) z)
    (a : ℂ) (ha : a ∈ ball c R \ sourcePeriodicSegment hp hp1 φ.val j)
    (he : F a = sourceAbelianJointPrimitive hp hp1 n (a,φ.val)) :
    EqOn F (fun z => sourceAbelianPrimitive hp hp1 φ.val φ.property z+I*(Real.pi : ℂ)*n)
      (ball c R \ sourcePeriodicSegment hp hp1 φ.val j) := by
  have hroot := sourceAbelian_discComplement_subset_rootDomain hp hp1 φ.val j c R hother
  apply sourceAbelian_complexDisc_unique hp hp1 φ.val j c R hseg F _ hF
    (fun z hz => (sourceAbelianPrimitive_hasDerivAt_quotient hp hp1 φ.val φ.property z (hroot hz)).add_const _)
    a ha
  exact he.trans (sourceAbelianJointPrimitive_eq_real hp hp1 n φ a (hroot ha))

/-- The signed index relation holds throughout the continued disc,
 independently of the primitives chosen to realize the continuation. -/
theorem sourceAbelian_complexDisc_eq_zeroIndex_add
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (j n : ℤ) (c : ℂ) (R : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 ψ j ⊆ ball c R)
    (F G : ℂ → ℂ)
    (hF : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j,
      HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z)
    (hG : ∀ z ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j,
      HasDerivAt G (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z)
    (a : ℂ) (ha : a ∈ ball c R \ sourcePeriodicSegment hp hp1 ψ j)
    (hajoint : (a,ψ) ∈ sourceAbelianJointDomain hp hp1)
    (hFa : F a = sourceAbelianJointPrimitive hp hp1 n (a,ψ))
    (hGa : G a = sourceAbelianJointPrimitive hp hp1 0 (a,ψ)) :
    EqOn F (fun z => G z+I*(Real.pi : ℂ)*n) (ball c R \ sourcePeriodicSegment hp hp1 ψ j) := by
  apply sourceAbelian_complexDisc_unique hp hp1 ψ j c R hseg F _ hF
    (fun z hz => (hG z hz).add_const _) a ha
  rw [hFa,hGa]
  exact sourceAbelianJointPrimitive_eq_zeroIndex_add hp hp1 n (a,ψ) hajoint

end NLS.ZakharovShabat
