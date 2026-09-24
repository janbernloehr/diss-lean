import NLS.ZakharovShabat.SourceActionAllGapPositive
import NLS.ZakharovShabat.SourceActionContourHomotopy

/-!
# Action signs on enclosing midpoint circles

An enclosing midpoint circle with a filled disc free of all other
periodic gaps has the same action as a sufficiently small midpoint
circle. Thus the open-gap positivity result holds on every such circle.
The collapsed-gap extension gives the complementary zero case.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any midpoint circle enclosing an open real gap, whose filled disc
avoids the other gaps, has a strictly positive real action. -/
theorem sourceActionCircle_positive_real_on_enclosing_midpointCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∀ R : ℝ, d < R →
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
      0 < (sourceActionCircle hp hp1 ψ c R).re ∧
        (sourceActionCircle hp hp1 ψ c R).im = 0 := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  obtain ⟨ε₁,hε₁,hpos⟩ :=
    exists_sourceActionCircle_positive_real_on_small_realGapCircles
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hgeom⟩ :=
    exists_sourceCriticalRootRatio_midpointCircle_mem_rootDomain
      hp hp1 ψ hreal n
  dsimp only
  intro R hR hother
  let η : ℝ := min ε₁ (min ε₂ (R-d))/2
  have hmargin : 0 < R-d := sub_pos.mpr hR
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (lt_min hε₁ (lt_min hε₂ hmargin)) (by norm_num)
  have hη₁ : η ∈ Ioc 0 ε₁ := by
    constructor
    · exact hη
    · dsimp [η]
      linarith [min_le_left ε₁ (min ε₂ (R-d))]
  have hη₂ : η ∈ Ioc 0 ε₂ := by
    constructor
    · exact hη
    · dsimp [η]
      linarith [min_le_right ε₁ (min ε₂ (R-d)),
        min_le_left ε₂ (R-d)]
  have hinnerR : d+η ≤ R := by
    dsimp [η]
    linarith [min_le_right ε₁ (min ε₂ (R-d)),
      min_le_right ε₂ (R-d)]
  have hinner := hgeom η hη₂
  have houterR : 0 < R := lt_of_lt_of_le hinner.1 hinnerR
  have houterSeg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R := by
    have h : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c (d+(R-d)) :=
      sourcePeriodicSegment_subset_midpoint_ball
        hp hp1 ψ hreal n (R-d) hmargin
    have hrad : d+(R-d)=R := by ring
    rw [hrad] at h
    exact h
  have hnest : closedBall c (d+η) ⊆ closedBall c R := by
    intro z hz
    exact mem_closedBall.mpr ((mem_closedBall.mp hz).trans hinnerR)
  have heq := sourceActionCircle_eq_of_nested_enclosingCircles
    hp hp1 ψ n c c (d+η) R hinner.1 houterR
      hinner.2.1 houterSeg hnest hother
  rw [← heq]
  exact hpos η hη₁

/-- On the same class of enclosing midpoint circles, a collapsed
real gap has zero action. -/
theorem sourceActionCircle_eq_zero_on_collapsed_enclosing_midpointCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∀ R : ℝ, d < R →
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
      sourceActionCircle hp hp1 ψ c R = 0 := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  dsimp only
  intro R hR hother
  have hrl : r = l := by
    have h : r-l = 0 := by
      simpa only [sourcePeriodicGapDisplacement_apply,
        canonicalPeriodicGap, r, l] using hgap
    exact sub_eq_zero.mp h
  have hd : d = 0 := by simp [d,hrl]
  have hRpos : 0 < R := by
    change d < R at hR
    simpa only [hd] using hR
  have hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R := by
    have h : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c (d+(R-d)) :=
      sourcePeriodicSegment_subset_midpoint_ball
        hp hp1 ψ hreal n (R-d) (sub_pos.mpr hR)
    have hrad : d+(R-d)=R := by ring
    rw [hrad] at h
    exact h
  have hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_enclosingCircle
      hp hp1 ψ n c R hseg hother
  obtain ⟨W,_,hWreal,hzero⟩ :=
    exists_global_sourceActionCircle_zero_of_zeroGap hp hp1
  have hψ : ψ ∈ W := hWreal hreal
  exact hzero ψ hψ n hgap c R hRpos.le hother hcircle

/-- On every isolating midpoint circle, the action is real and
nonnegative, and it vanishes exactly when the selected gap collapses. -/
theorem sourceActionCircle_nonneg_and_eq_zero_iff_gap_zero_on_midpointCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∀ R : ℝ, d < R →
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
      0 ≤ (sourceActionCircle hp hp1 ψ c R).re ∧
        (sourceActionCircle hp hp1 ψ c R).im = 0 ∧
        (sourceActionCircle hp hp1 ψ c R = 0 ↔
          sourcePeriodicGapDisplacement hp hp1 ψ n = 0) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  dsimp only
  intro R hR hother
  have hle : l.re ≤ r.re :=
    re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ)).2.1 n)
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  by_cases hopen : l.re < r.re
  · have hA := sourceActionCircle_positive_real_on_enclosing_midpointCircle
      hp hp1 ψ hreal n hopen R hR hother
    refine ⟨hA.1.le,hA.2,?_⟩
    have hgapNe : sourcePeriodicGapDisplacement hp hp1 ψ n ≠ 0 := by
      intro hgap
      have h : r-l=0 := by
        simpa only [sourcePeriodicGapDisplacement_apply,
          canonicalPeriodicGap, r, l] using hgap
      have heq : r = l := sub_eq_zero.mp h
      have hre := congrArg Complex.re heq
      exact (ne_of_gt hopen) hre
    constructor
    · intro hzero
      have hre := congrArg Complex.re hzero
      simp only [Complex.zero_re] at hre
      exact False.elim ((ne_of_gt hA.1) hre)
    · intro hzero
      exact False.elim (hgapNe hzero)
  · have hre : l.re = r.re := le_antisymm hle (le_of_not_gt hopen)
    have hlr : l = r := by
      apply Complex.ext
      · exact hre
      · exact him.1.trans him.2.symm
    have hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0 := by
      simp only [sourcePeriodicGapDisplacement_apply, canonicalPeriodicGap]
      change r-l=0
      rw [hlr]
      exact sub_self _
    have hA := sourceActionCircle_eq_zero_on_collapsed_enclosing_midpointCircle
      hp hp1 ψ hreal n hgap R hR hother
    rw [hA]
    exact ⟨le_refl _,by simp, ⟨by intro _; exact hgap, by intro _; rfl⟩⟩

end NLS.ZakharovShabat
