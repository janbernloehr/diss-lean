import NLS.ZakharovShabat.SourcePsiCollapsedGapOffsetGeometry
import NLS.ZakharovShabat.SourcePsiGapProductDiscBound
import NLS.ZakharovShabat.SourcePsiMidpointNormalizedOffset
import NLS.ZakharovShabat.SourcePsiLocalAssignedContourZero
import NLS.ZakharovShabat.SourcePsiQuotientUniformGapProductTail
import NLS.ZakharovShabat.SourcePsiUniformFilledBranchStability

/-!
# Uniform finite-head squared-gap offsets for the actual psi roots

At a collapsed reference gap, a fixed small circle inside its assigned
disc separates every other moving midpoint. Uniform filled-branch
stability, compact quotient bounds, and the actual retained contour
zero give a quadratic gap estimate independent of the omitted index.
At a noncollapsed reference gap, continuity keeps the gap bounded
away from zero and assigned root placement bounds the offset. A
finite intersection gives a common bound for any selected finite head.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourcePsiIsolatingComplexRootAtlas.exists_local_collapsed_gap_squared_offset_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
    (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U) (φ : realTypeSourceLocus p)
    (m : ℤ) (hγ : sourcePeriodicGapDisplacement hp hp1 φ.val m = 0) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
      V ⊆ A.toSourcePsiComplexRootAtlas.sourceBall φ ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ V, ∀ n : ℤ, m ≠ n →
        ‖displacedRoots (A.toSourcePsiComplexRootAtlas.branch n ψ : Coeff p) m-
          sourceStandardRootMidpoint hp hp1 ψ m‖ ≤ C*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 := by
  let B := A.toSourcePsiComplexRootAtlas
  let c := sourceStandardRootMidpoint hp hp1 φ.val m
  obtain ⟨r,hr,hclosed2,Vg,hVg,hφVg,hVgBall,hsmall⟩ :=
    A.exists_local_collapsed_gap_offset_circle φ m hγ
  have hclosed : closedBall c r ⊆
      sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m :=
    (closedBall_subset_closedBall (by linarith : r ≤ 2*r)).trans hclosed2
  have hbase : φ.val ∈ B.sourceBall φ := mem_ball_self (B.localBranch φ).sourceRadius_pos
  have hdomBase : closedBall c r ⊆ sourceStandardRootOmittedDomain hp hp1 φ.val m :=
    hclosed.trans (sourceIsolatingDisc_subset_omittedDomain hp hp1 φ.val φ.val
      (A.cutoff φ) (A.enlargement φ) (A.clusters φ φ.val hbase) (A.disjoint φ) m)
  obtain ⟨δu,M,hδu,hM,hupper⟩ :=
    exists_sourcePsiQuotient_disc_bound_near_gapProduct hp hp1 φ m c r hdomBase
  obtain ⟨δl,c₀,hδl,hc₀,hlower⟩ :=
    exists_sourcePsi_midpointQuotient_uniform_lowerBound_near_gapProduct hp hp1 φ
  let δ := min δu δl
  obtain ⟨ρ,hρ,hρS,hgraph⟩ := (B.localBranch φ).exists_uniform_midpointFilled_graph_radius δ (lt_min hδu hδl)
  obtain ⟨rz,hrz,_,hzeroAssigned⟩ := A.exists_local_assigned_contour_zero φ
  obtain ⟨W,hW,_,hreal,hQ⟩ := exists_global_source_analytic_singleRootQuotient hp hp1
  let V := ball φ.val ρ ∩ (Vg ∩ (ball φ.val rz ∩ W))
  let ci := sourceIsolatingCenter hp hp1 φ.val (A.cutoff φ) m
  let Ri := sourceIsolatingRadius hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m
  let S := Ri+‖ci-c‖+r
  have hRi : 0 < Ri := sourceIsolatingRadius_pos hp hp1 φ.val (A.cutoff φ)
    (A.enlargement φ) (A.enlargement_pos φ) m
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let C := (r*S/((r/2)^3*c₀))*3*M
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨V,isOpen_ball.inter (hVg.inter (isOpen_ball.inter hW)),
    ⟨mem_ball_self hρ,hφVg,mem_ball_self hrz,hreal φ.property⟩,
    (fun ψ hψ => hVgBall hψ.2.1),C,hC,?_⟩
  intro ψ hψ n hmn
  have hψBall : ψ ∈ B.sourceBall φ := hVgBall hψ.2.1
  obtain ⟨hmidSmall,hgap⟩ := hsmall ψ hψ.2.1
  have hgapAll k : sourcePeriodicSegment hp hp1 ψ k ⊆
      sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) k :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val ψ (A.cutoff φ) (A.enlargement φ) k
      (A.clusters φ ψ hψBall k)
  have hdom : closedBall c r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    hclosed.trans (sourceIsolatingDisc_subset_omittedDomain hp hp1 φ.val ψ
      (A.cutoff φ) (A.enlargement φ) (A.clusters φ ψ hψBall) (A.disjoint φ) m)
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r :=
    sourcePeriodicSegment_subset_ball_of_small_midpoint_gap hp hp1 ψ m c r hr hmidSmall hgap
  have hcircle : sphere c r ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    intro z hz k
    by_cases hkm : k = m
    · subst k
      intro hk
      exact (ne_of_lt (mem_ball.mp (hseg hk))) (mem_sphere.mp hz)
    · exact hdom (sphere_subset_closedBall hz) k hkm
  have hfamily := sourcePsiAssignedCircleFamily hp hp1 φ.val ψ (A.cutoff φ) (A.enlargement φ)
    (A.enlargement_pos φ) hgapAll (A.disjoint φ)
  have hnest : closedBall c r ⊆ closedBall ci Ri := by
    have hball : sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m ⊆ closedBall ci Ri := by
      rw [sourceIsolatingDisc_eq_ball]
      exact ball_subset_closedBall
    exact hclosed.trans hball
  have hzero : sourcePsiContour hp hp1 n (B.branch n ψ : Coeff p) ψ c r = 0 := by
    rw [sourcePsiContour_eq_of_nested_enclosingCircles hp hp1 n m (B.branch n ψ : Coeff p) ψ
      c ci r Ri hr hRi hseg (hfamily.2 m).2.1 hnest (hfamily.2 m).2.2.1]
    exact hzeroAssigned ψ hψ.2.2.1 n m hmn
  let q := (sourcePsiFillDeletedRoot n (B.branch n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ)
  let q₀ := (sourcePsiFillDeletedRoot n (sourcePsiGapRoot hp hp1 n φ)
    (sourceStandardRootMidpoint hp hp1 φ.val n),φ.val)
  let K := sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}
  have hq₀ : q₀ ∈ K := ⟨sourcePsiGapRoot_filled_mem_periodicGapRootSet hp hp1 φ n,rfl⟩
  have hnear := hgraph ψ hψ.1 n
  rw [← B.eq_local n φ hψBall] at hnear
  have hq : q ∈ cthickening δ K := mem_cthickening_of_dist_le q q₀ δ K hq₀ hnear.le
  have hqu : q ∈ cthickening δu K := cthickening_mono (min_le_left _ _) K hq
  have hql : q ∈ cthickening δl K := cthickening_mono (min_le_right _ _) K hq
  have hQA : AnalyticOnNhd ℂ (fun z => sourceSingleRootQuotientJointProduct hp hp1 m (z,q)) (closedBall c r) := by
    intro z hz
    have hinc : AnalyticAt ℂ (fun w : ℂ => (w,q)) z := analyticAt_id.prod analyticAt_const
    exact ((hQ m).2 (z,q) ⟨hψ.2.2.2,hdom hz⟩).comp (x := z) (f := fun w : ℂ => (w,q)) hinc
  have hτn : sourceStandardRootMidpoint hp hp1 ψ n ∈
      sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) n :=
    hgapAll n (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have hτnOutside : sourceStandardRootMidpoint hp hp1 ψ n ∉ ball c (2*r) := by
    intro hin
    exact Set.disjoint_left.mp (A.disjoint φ m n hmn) (hclosed2 (ball_subset_closedBall hin)) hτn
  have hden z (hz : z ∈ closedBall c r) : r ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖ := by
    have hn : 2*r ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-c‖ := by
      exact not_lt.mp (by simpa only [mem_ball,dist_eq_norm] using hτnOutside)
    have hzNorm : ‖z-c‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have htri : ‖sourceStandardRootMidpoint hp hp1 ψ n-c‖ ≤
        ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖+‖z-c‖ := by
      calc
        _ = ‖(sourceStandardRootMidpoint hp hp1 ψ n-z)+(z-c)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    linarith only [hn,hzNorm,htri]
  have hmid z (hz : z ∈ closedBall c r) : ‖z-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤ 2*r := by
    have hzNorm : ‖z-c‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hmidrev : ‖c-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤ r/4 := by
      rw [norm_sub_rev]
      exact hmidSmall
    have htri : ‖z-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤ ‖z-c‖+‖c-sourceStandardRootMidpoint hp hp1 ψ m‖ := by
      calc
        _ = ‖(z-c)+(c-sourceStandardRootMidpoint hp hp1 ψ m)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    linarith only [hzNorm,hmidrev,htri,hr]
  have hsep z (hz : z ∈ sphere c r) : r/2 ≤ ‖sourceStandardRootMidpoint hp hp1 ψ m-z‖ := by
    have hzNorm : ‖c-z‖ = r := by
      rw [norm_sub_rev]
      exact (by simpa only [mem_sphere,dist_eq_norm] using hz)
    have hmidrev : ‖c-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤ r/4 := by
      rw [norm_sub_rev]
      exact hmidSmall
    have htri : ‖c-z‖ ≤ ‖c-sourceStandardRootMidpoint hp hp1 ψ m‖+‖sourceStandardRootMidpoint hp hp1 ψ m-z‖ := by
      calc
        _ = ‖(c-sourceStandardRootMidpoint hp hp1 ψ m)+(sourceStandardRootMidpoint hp hp1 ψ m-z)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    linarith only [hzNorm,hmidrev,htri,hr]
  have hσ z (hz : z ∈ sphere c r) : ‖displacedRoots (B.branch n ψ : Coeff p) m-z‖ ≤ S := by
    have hplace := A.global_placement φ n ψ hψBall m hmn
    rw [sourceIsolatingDisc_eq_ball,mem_ball,dist_eq_norm] at hplace
    have hzNorm : ‖c-z‖ = r := by
      rw [norm_sub_rev]
      exact (by simpa only [mem_sphere,dist_eq_norm] using hz)
    have htri : ‖displacedRoots (B.branch n ψ : Coeff p) m-z‖ ≤
        ‖displacedRoots (B.branch n ψ : Coeff p) m-ci‖+‖ci-c‖+‖c-z‖ := by
      have heq : displacedRoots (B.branch n ψ : Coeff p) m-z =
          (displacedRoots (B.branch n ψ : Coeff p) m-ci)+(ci-c)+(c-z) := by ring
      rw [heq]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have hplace' : ‖displacedRoots (B.branch n ψ : Coeff p) m-ci‖ < Ri := hplace
    dsimp only [S]
    linarith only [hplace',hzNorm,htri]
  have h := norm_sourcePsi_midpointNormalized_root_offset_le hp hp1 n m hmn (B.branch n ψ) ψ c r hr
    hseg hcircle hzero hQA r (r/2) (2*r) S M c₀ hr (by positivity) (by positivity) hS hM hc₀
    hden hmid hsep hgap hσ (hupper q hqu) (hlower q hql m)
  have hthree : 1+2*r/r = 3 := by field_simp [hr.ne']; ring
  rw [hthree] at h
  exact h

/-- A reference gap that is nonzero stays separated from zero on
one source neighborhood. Assigned root placement then gives a common
quadratic offset bound for every omitted index. -/
theorem SourcePsiIsolatingComplexRootAtlas.exists_local_noncollapsed_gap_squared_offset_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
    (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U) (φ : realTypeSourceLocus p)
    (m : ℤ) (hγ : sourcePeriodicGapDisplacement hp hp1 φ.val m ≠ 0) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
      V ⊆ A.toSourcePsiComplexRootAtlas.sourceBall φ ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ V, ∀ n : ℤ, m ≠ n →
        ‖displacedRoots (A.toSourcePsiComplexRootAtlas.branch n ψ : Coeff p) m-
          sourceStandardRootMidpoint hp hp1 ψ m‖ ≤ C*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 := by
  let B := A.toSourcePsiComplexRootAtlas
  let g := ‖sourcePeriodicGapDisplacement hp hp1 φ.val m‖/2
  have hg : 0 < g := half_pos (norm_pos_iff.mpr hγ)
  have hgapCont : ContinuousAt (fun ψ : CoeffPair p => sourcePeriodicGapDisplacement hp hp1 ψ m) φ.val :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).continuous.continuousAt.comp
      (continuousAt_sourcePeriodicGapDisplacement_of_realType hp hp1 φ.val φ.property)
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hgapCont g hg
  let V := ball φ.val δ ∩ B.sourceBall φ
  let ci := sourceIsolatingCenter hp hp1 φ.val (A.cutoff φ) m
  let Ri := sourceIsolatingRadius hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m
  have hRi : 0 < Ri := sourceIsolatingRadius_pos hp hp1 φ.val (A.cutoff φ)
    (A.enlargement φ) (A.enlargement_pos φ) m
  let C := 2*Ri/g^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨V,isOpen_ball.inter isOpen_ball,
    ⟨mem_ball_self hδ,mem_ball_self (B.localBranch φ).sourceRadius_pos⟩,
    inter_subset_right,C,hC,?_⟩
  intro ψ hψ n hmn
  have hnear : ‖sourcePeriodicGapDisplacement hp hp1 ψ m-sourcePeriodicGapDisplacement hp hp1 φ.val m‖ < g := by
    simpa only [dist_eq_norm] using hclose (mem_ball.mp hψ.1)
  have hglower : g ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ := by
    have htri := norm_sub_norm_le (sourcePeriodicGapDisplacement hp hp1 φ.val m)
      (sourcePeriodicGapDisplacement hp hp1 ψ m)
    rw [norm_sub_rev] at htri
    dsimp only [g] at *
    linarith only [htri,hnear]
  have hroot := A.global_placement φ n ψ hψ.2 m hmn
  have hmid := sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val ψ
    (A.cutoff φ) (A.enlargement φ) m (A.clusters φ ψ hψ.2 m)
    (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m)
  rw [sourceIsolatingDisc_eq_ball,mem_ball,dist_eq_norm] at hroot hmid
  have hroot' : ‖displacedRoots (B.branch n ψ : Coeff p) m-ci‖ < Ri := hroot
  have hmid' : ‖ci-sourceStandardRootMidpoint hp hp1 ψ m‖ < Ri := by
    rw [norm_sub_rev]
    exact hmid
  have hoffset : ‖displacedRoots (B.branch n ψ : Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤ 2*Ri := by
    have htri : ‖displacedRoots (B.branch n ψ : Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤
        ‖displacedRoots (B.branch n ψ : Coeff p) m-ci‖+‖ci-sourceStandardRootMidpoint hp hp1 ψ m‖ := by
      have heq : displacedRoots (B.branch n ψ : Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m =
          (displacedRoots (B.branch n ψ : Coeff p) m-ci)+(ci-sourceStandardRootMidpoint hp hp1 ψ m) := by ring
      rw [heq]
      exact norm_add_le _ _
    linarith only [htri,hroot',hmid']
  have hsq : g^2 ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 :=
    pow_le_pow_left₀ hg.le hglower 2
  calc
    _ ≤ 2*Ri := hoffset
    _ = C*g^2 := by dsimp [C]; rw [div_mul_cancel₀ _ (pow_ne_zero 2 hg.ne')]
    _ ≤ C*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 :=
      mul_le_mul_of_nonneg_left hsq hC

/-- Any selected finite head has a quadratic-gap offset estimate for
the actual analytic roots on one complex source neighborhood, with
one constant for all omitted indices and including collapsed gaps. -/
theorem SourcePsiIsolatingComplexRootAtlas.exists_local_finiteHead_squared_offset_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}
    (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U) (φ : realTypeSourceLocus p) (s : Finset ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
      V ⊆ A.toSourcePsiComplexRootAtlas.sourceBall φ ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ V, ∀ n : ℤ, ∀ m ∈ s, m ≠ n →
        ‖displacedRoots (A.toSourcePsiComplexRootAtlas.branch n ψ : Coeff p) m-
          sourceStandardRootMidpoint hp hp1 ψ m‖ ≤ C*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 := by
  classical
  have hlocal (m : ℤ) : ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
      V ⊆ A.toSourcePsiComplexRootAtlas.sourceBall φ ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ V, ∀ n : ℤ, m ≠ n →
        ‖displacedRoots (A.toSourcePsiComplexRootAtlas.branch n ψ : Coeff p) m-
          sourceStandardRootMidpoint hp hp1 ψ m‖ ≤ C*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 := by
    by_cases hγ : sourcePeriodicGapDisplacement hp hp1 φ.val m = 0
    · exact A.exists_local_collapsed_gap_squared_offset_bound φ m hγ
    · exact A.exists_local_noncollapsed_gap_squared_offset_bound φ m hγ
  choose V hV hφV hVBall C hC hbound using hlocal
  let B := A.toSourcePsiComplexRootAtlas
  let O := B.sourceBall φ ∩ ⋂ m ∈ s, V m
  let M := ∑ m ∈ s, C m
  have hO : IsOpen O := isOpen_ball.inter (isOpen_biInter_finset (fun m _ => hV m))
  have hφO : φ.val ∈ O := by
    refine ⟨mem_ball_self (B.localBranch φ).sourceRadius_pos,?_⟩
    simp only [Set.mem_iInter]
    exact fun m _ => hφV m
  refine ⟨O,hO,hφO,inter_subset_left,M,Finset.sum_nonneg (fun m _ => hC m),?_⟩
  intro ψ hψ n m hm hmn
  have hψV : ψ ∈ V m := (mem_iInter.mp (mem_iInter.mp hψ.2 m)) hm
  have hCm : C m ≤ M := Finset.single_le_sum (fun k _ => hC k) hm
  exact (hbound m ψ hψV n hmn).trans (mul_le_mul_of_nonneg_right hCm (sq_nonneg _))

end NLS.ZakharovShabat
