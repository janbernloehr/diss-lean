import NLS.ZakharovShabat.SourcePeriodicMidpointGapContinuity
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles
import NLS.ZakharovShabat.SourcePsiFreeLatticeBound

/-!
# One source neighborhood for every free-centered psi contour

Sequence-norm continuity of periodic midpoint and gap displacements
makes every moving source gap small at once. Around the free source,
all periodic segments lie in disjoint eighth-π lattice discs. Thus a
quarter-π disc around index `m` avoids every gap except the selected
one, with no finite-index exceptions.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Both periodic midpoint and gap displacement sequences vanish at
the free source. -/
theorem sourcePeriodicMidpointDisplacement_zero_source
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sourcePeriodicMidpointDisplacement hp hp1 (0 : CoeffPair p) = 0 := by
  ext m
  simp only [sourcePeriodicMidpointDisplacement_apply, map_zero,
    canonicalPeriodicMidpoint_zero, sub_self, lp.coeFn_zero, Pi.zero_apply]

theorem sourcePeriodicGapDisplacement_zero_source
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sourcePeriodicGapDisplacement hp hp1 (0 : CoeffPair p) = 0 := by
  ext m
  simp only [sourcePeriodicGapDisplacement_apply, map_zero,
    canonicalPeriodicGap_zero, lp.coeFn_zero, Pi.zero_apply]

/-- Every moving periodic segment fits into its free eighth-π disc
on a single open source neighborhood. -/
theorem exists_nearFree_allPeriodicSegments_in_eighth_ball
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, ∀ m : ℤ,
        sourcePeriodicSegment hp hp1 ψ m ⊆
          ball ((Real.pi : ℂ)*m) (Real.pi/8) := by
  have hmidCont := continuousAt_sourcePeriodicMidpointDisplacement_of_realType
    hp hp1 (0 : CoeffPair p) (by simp)
  have hgapCont := continuousAt_sourcePeriodicGapDisplacement_of_realType
    hp hp1 (0 : CoeffPair p) (by simp)
  obtain ⟨δm,hδm,hmid⟩ := Metric.continuousAt_iff.mp hmidCont
    (Real.pi/64) (by positivity)
  obtain ⟨δg,hδg,hgap⟩ := Metric.continuousAt_iff.mp hgapCont
    (Real.pi/32) (by positivity)
  let δ := min δm δg
  have hδ : 0 < δ := lt_min hδm hδg
  refine ⟨ball 0 δ,isOpen_ball,mem_ball_self hδ,?_⟩
  intro ψ hψ m
  have hψm : dist ψ (0 : CoeffPair p) < δm :=
    (mem_ball.mp hψ).trans_le (min_le_left _ _)
  have hψg : dist ψ (0 : CoeffPair p) < δg :=
    (mem_ball.mp hψ).trans_le (min_le_right _ _)
  have hmnorm : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ <
      Real.pi/64 := by
    have h := hmid hψm
    rw [sourcePeriodicMidpointDisplacement_zero_source hp hp1,
      dist_zero_right] at h
    exact h
  have hgnorm : ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ <
      Real.pi/32 := by
    have h := hgap hψg
    rw [sourcePeriodicGapDisplacement_zero_source hp hp1,
      dist_zero_right] at h
    exact h
  have hmidpoint : ‖sourceStandardRootMidpoint hp hp1 ψ m -
      (Real.pi : ℂ)*m‖ ≤ Real.pi/64 := by
    have hcoord := lp.norm_apply_le_norm
      (ne_of_gt (zero_lt_one.trans_le Fact.out))
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) m
    have hc : ‖sourceStandardRootMidpoint hp hp1 ψ m -
        (Real.pi : ℂ)*m‖ ≤
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ := by
      simpa only [sourcePeriodicMidpointDisplacement_apply,
        sourceStandardRootMidpoint] using hcoord
    exact (hc.trans_lt hmnorm).le
  have hgapcoord : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤
      Real.pi/32 :=
    (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le Fact.out))
      (sourcePeriodicGapDisplacement hp hp1 ψ) m).trans hgnorm.le
  exact sourcePeriodicSegment_subset_free_eighth_ball
    hp hp1 ψ m hmidpoint hgapcoord

/-- A free quarter-π disc cannot meet an eighth-π disc at a different
lattice index. -/
theorem free_quarter_closedBall_disjoint_other_eighth_ball
    (m k : ℤ) (hmk : m ≠ k) :
    Disjoint (closedBall ((Real.pi : ℂ)*m) (Real.pi/4))
      (ball ((Real.pi : ℂ)*k) (Real.pi/8)) := by
  apply Set.disjoint_left.mpr
  intro z hzm hzk
  have habs : (1 : ℝ) ≤ |((k-m : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hmk))
  have hcenters : dist ((Real.pi : ℂ)*k) ((Real.pi : ℂ)*m) =
      Real.pi * |((k-m : ℤ) : ℝ)| := by
    simpa only [dist_eq_norm] using norm_free_center_sub k m
  have htri := dist_triangle ((Real.pi : ℂ)*k) z ((Real.pi : ℂ)*m)
  rw [hcenters] at htri
  have hk : dist ((Real.pi : ℂ)*k) z < Real.pi/8 := by
    simpa only [dist_comm] using (mem_ball.mp hzk)
  have hm := mem_closedBall.mp hzm
  have hsep := mul_le_mul_of_nonneg_left habs Real.pi_pos.le
  nlinarith [Real.pi_pos]

/-- On that neighborhood, every free quarter-π disc is contained in
the omitted-root domain for its selected index. -/
theorem exists_nearFree_freeQuarterDisc_subset_omittedDomain
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, ∀ m : ℤ,
        closedBall ((Real.pi : ℂ)*m) (Real.pi/4) ⊆
          sourceStandardRootOmittedDomain hp hp1 ψ m := by
  obtain ⟨V,hVopen,hzero,hsegments⟩ :=
    exists_nearFree_allPeriodicSegments_in_eighth_ball hp hp1
  refine ⟨V,hVopen,hzero,?_⟩
  intro ψ hψ m z hz k hkm hzk
  exact (Set.disjoint_left.mp
    (free_quarter_closedBall_disjoint_other_eighth_ball m k (Ne.symm hkm)))
      hz (hsegments ψ hψ k hzk)

/-- The common free eighth-π circles avoid every moving periodic
gap on the same source neighborhood. -/
theorem exists_nearFree_freeEighthCircle_subset_rootDomain
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧
      ∀ ψ ∈ V, ∀ m : ℤ,
        sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
          sourceCanonicalRootDomain hp hp1 ψ := by
  obtain ⟨V,hVopen,hzero,hsegments⟩ :=
    exists_nearFree_allPeriodicSegments_in_eighth_ball hp hp1
  refine ⟨V,hVopen,hzero,?_⟩
  intro ψ hψ m z hz k
  by_cases hmk : m = k
  · subst k
    intro hmem
    have hball := hsegments ψ hψ m hmem
    have hsphere := mem_sphere.mp hz
    have hlt := mem_ball.mp hball
    exact (ne_of_lt hlt) hsphere
  · intro hmem
    have hzquarter : z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/4) :=
      (Metric.closedBall_subset_closedBall (by nlinarith [Real.pi_pos]))
        (sphere_subset_closedBall hz)
    exact (Set.disjoint_left.mp
      (free_quarter_closedBall_disjoint_other_eighth_ball m k hmk))
        hzquarter (hsegments ψ hψ k hmem)

end NLS.ZakharovShabat
