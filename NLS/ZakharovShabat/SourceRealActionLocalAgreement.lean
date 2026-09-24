import NLS.ZakharovShabat.SourceRealActionLocalCircleStability

/-!
# Local agreement with the real indexed action

The fixed midpoint circle chosen at a real-type source continues to
compute the indexed action at every nearby real-type source. A smaller
midpoint circle for the moving gap fits in the fixed disc, and the
weighted contour integral is invariant under the nested-circle homotopy.
-/

noncomputable section
open Set Metric Filter Topology Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near a real-type source, one fixed contour represents the indexed
real action at every real-type source in the neighborhood. -/
theorem exists_local_circle_agrees_with_sourceRealAction
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        ∀ ψ ∈ V, ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
          sourceRealAction hp hp1 ψ hψ n =
            sourceActionCircle hp hp1 ψ c R := by
  let L : CoeffPair p → ℂ := fun ψ =>
    canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
  let Rt : CoeffPair p → ℂ := fun ψ =>
    canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
  let mid : CoeffPair p → ℂ := fun ψ => (((L ψ).re+(Rt ψ).re)/2:ℝ)
  let half : CoeffPair p → ℝ := fun ψ => ((Rt ψ).re-(L ψ).re)/2
  obtain ⟨c,R,hR,hc,hdR,V₀,hV₀open,hφV₀,_,hgeom⟩ :=
    exists_local_stable_midpointCircle_through_sourceRealAction
      hp hp1 φ hreal n
  have hmidφ : mid φ = c := hc.symm
  have hdR' : half φ < R := hdR
  let q : ℝ := (R-half φ)/2
  have hq : 0 < q := by dsimp [q]; linarith [hdR']
  have hLcont : ContinuousAt L φ :=
    continuousAt_canonicalPeriodicLeft_periodOne_of_realType
      hp hp1 φ hreal n
  have hRtcont : ContinuousAt Rt φ :=
    continuousAt_canonicalPeriodicRight_periodOne_of_realType
      hp hp1 φ hreal n
  have hLre : ContinuousAt (fun ψ => (L ψ).re) φ :=
    continuous_re.continuousAt.comp hLcont
  have hRre : ContinuousAt (fun ψ => (Rt ψ).re) φ :=
    continuous_re.continuousAt.comp hRtcont
  have hmidcont : ContinuousAt mid φ := by
    exact continuous_ofReal.continuousAt.comp ((hLre.add hRre).div_const 2)
  have hhalfcont : ContinuousAt half φ := by
    exact (hRre.sub hLre).div_const 2
  have hmargincont : ContinuousAt
      (fun ψ => half ψ + q + dist (mid ψ) c) φ := by
    exact (hhalfcont.add_const q).add
      (continuous_dist.continuousAt.comp (hmidcont.prodMk continuousAt_const))
  have hmarginφ : half φ + q + dist (mid φ) c < R := by
    rw [hmidφ,dist_self]
    dsimp [q]
    linarith [hdR']
  have hnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      half ψ + q + dist (mid ψ) c < R :=
    hmargincont.eventually (isOpen_Iio.mem_nhds hmarginφ)
  obtain ⟨V₁,hV₁sub,hV₁open,hφV₁⟩ := _root_.mem_nhds_iff.mp hnear
  let V := V₀ ∩ V₁
  refine ⟨c,R,hR,V,hV₀open.inter hV₁open,⟨hφV₀,hφV₁⟩,?_,?_⟩
  · intro ψ hψ
    exact hgeom ψ hψ.1
  intro ψ hψ hψreal
  let r : ℝ := half ψ + q
  have hhalf : 0 ≤ half ψ := by
    have hle := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ)).2.1 n)
    change 0 ≤ ((Rt ψ).re-(L ψ).re)/2
    exact div_nonneg (sub_nonneg.mpr hle) (by norm_num)
  have hr : 0 < r := by dsimp [r]; linarith
  have hnest : closedBall (mid ψ) r ⊆ closedBall c R :=
    closedBall_subset_closedBall' (le_of_lt (hV₁sub hψ.2))
  have hinnerOther : closedBall (mid ψ) r ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n :=
    hnest.trans (hgeom ψ hψ.1).2
  have hinnerValue : sourceRealAction hp hp1 ψ hψreal n =
      sourceActionCircle hp hp1 ψ (mid ψ) r :=
    sourceRealAction_eq_enclosing_midpointCircle
      hp hp1 ψ hψreal n r (by change half ψ < r; dsimp [r]; linarith)
      hinnerOther
  have hinnerSeg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball (mid ψ) r :=
    sourcePeriodicSegment_subset_midpoint_ball hp hp1 ψ hψreal n q hq
  exact hinnerValue.trans
    (sourceActionCircle_eq_of_nested_enclosingCircles
      hp hp1 ψ n (mid ψ) c r R hr hR hinnerSeg
      (hgeom ψ hψ.1).1 hnest (hgeom ψ hψ.1).2)

/-- The indexed action on nearby real-type sources is the restriction
of one complex-differentiable fixed-circle action. -/
theorem exists_local_differentiable_extension_of_sourceRealAction
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        DifferentiableOn ℂ
          (fun ψ : CoeffPair p => sourceActionCircle hp hp1 ψ c R) V ∧
        ∀ ψ ∈ V, ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
          sourceRealAction hp hp1 ψ hψ n =
            sourceActionCircle hp hp1 ψ c R := by
  obtain ⟨c,R,hR,V₀,hV₀open,hφV₀,hgeom,hagree⟩ :=
    exists_local_circle_agrees_with_sourceRealAction hp hp1 φ hreal n
  obtain ⟨W,_,_,hWreal,hDopen,hweighted⟩ :=
    exists_global_sourceActionIntegrand_jointAnalytic hp hp1
  have hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n c R
      (hgeom φ hφV₀).1 (hgeom φ hφV₀).2
  have hbase (z : ℂ) (hz : z ∈ sphere c R) :
      (z,φ) ∈ sourceCanonicalRootJointDomain hp hp1 W :=
    ⟨hWreal hreal,hcircle hz⟩
  obtain ⟨V₁,hV₁open,hφV₁,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      (sourceActionIntegrandJoint hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W)
      hDopen hweighted c R φ hbase
  let V := V₀ ∩ V₁
  have hVopen : IsOpen V := hV₀open.inter hV₁open
  refine ⟨c,R,hR,V,hVopen,⟨hφV₀,hφV₁⟩,?_,?_,?_⟩
  · intro ψ hψ
    exact hgeom ψ hψ.1
  · intro ψ hψ
    have hdiff :=
      NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
        (sourceActionIntegrandJoint hp hp1)
        (sourceCanonicalRootJointDomain hp hp1 W)
        hDopen hweighted c R hR.le V hVopen ψ hψ M
        (fun b hb θ => (hbound (circleMap c R θ)
          (circleMap_mem_sphere c hR.le θ) b hb.2).1)
        (fun b hb θ => (hbound (circleMap c R θ)
          (circleMap_mem_sphere c hR.le θ) b hb.2).2)
    change DifferentiableWithinAt ℂ
      (fun b : CoeffPair p => (Real.pi : ℂ)⁻¹ *
        ∮ z in C(c,R), sourceActionIntegrandJoint hp hp1 (z,b)) V ψ
    exact (hdiff.const_mul (Real.pi : ℂ)⁻¹).differentiableWithinAt
  · intro ψ hψ hψreal
    exact hagree ψ hψ.1 hψreal

end NLS.ZakharovShabat
