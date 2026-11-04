import NLS.KdV.HillAbelianCircleBound
import NLS.ComplexAnalysis.RealSegmentCommonCircle

/-! A finite selected gap has a common enclosing circle for both
signed terms of the ACTUAL Hill numerator. It encloses the ACTUAL
auxiliary divisor on one complex source neighborhood, including collapse. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_reflected_abelian_circle_chart (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ c : ℂ, ∃ r ρ : ℝ, 0 < r ∧ r < ρ ∧
      (∀ w ∈ closedBall c ρ,
        w ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ∧
        -w ∈ ball (P.centers (-((m:ℕ):ℤ)):ℂ) (P.radii (-((m:ℕ):ℤ)))) ∧
      ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
        ∀ a ∈ U, sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ) ⊆ ball c r ∧
          P.physicalDirichletFrequency ((m:ℕ):ℤ) a ∈ closedBall c r := by
  let k : ℤ := ((m:ℕ):ℤ)
  let l := canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) k
  let u := canonicalPeriodicRight (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) k
  let v : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := (hillMiuraRealSource v).property
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType (by norm_num) (by norm_num)
    (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) (isRealType_periodOnePotential _ hreal) k
  change l.im = 0 ∧ u.im = 0 at him
  have hl : (l.re:ℂ) = l := by simpa [him.1] using Complex.re_add_im l
  have hu : (u.re:ℂ) = u := by simpa [him.2] using Complex.re_add_im u
  have hp : sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) k ⊆
      ball (P.centers k:ℂ) (P.radii k) := by
    rw [← P.discs_eq]
    exact P.isolating.gap (P.sourcePsi q) (P.image q hq).2 k
  have href : SourcePeriodicReflection (by norm_num) (by norm_num) (P.sourcePsi q) :=
    sourcePeriodicReflection_hillMiuraDiagonal (P.parent.parent.miuraBall.actionBall.lift q)
  have hn (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) k) :
      z ∈ ball ((-P.centers (-k):ℝ):ℂ) (P.radii (-k)) := by
    have hneg := P.isolating.gap (P.sourcePsi q) (P.image q hq).2 (-k)
      ((href.neg_mem_segment_iff k z).mpr hz)
    rw [P.discs_eq] at hneg
    have hd := dist_neg_neg z (-(P.centers (-k):ℂ))
    simp only [neg_neg] at hd
    rw [mem_ball,Complex.ofReal_neg,← hd]
    exact hneg
  obtain ⟨c,r,ρ,hrpos,hrρ,hseg,hclosed⟩ := exists_common_circle_of_real_segment_in_two_balls
    l.re u.re (P.centers k) (-P.centers (-k)) (P.radii k) (P.radii (-k))
    (hl.symm ▸ hp (left_mem_segment ℝ _ _)) (hu.symm ▸ hp (right_mem_segment ℝ _ _))
    (hl.symm ▸ hn l (left_mem_segment ℝ _ _)) (hu.symm ▸ hn u (right_mem_segment ℝ _ _))
  have hseg' : sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) k ⊆ ball c r := by
    change segment ℝ l u ⊆ _
    rw [← hl,← hu]
    exact hseg
  have hclosed' (w : ℂ) (hw : w ∈ closedBall c ρ) :
      w ∈ ball (P.centers k:ℂ) (P.radii k) ∧ -w ∈ ball (P.centers (-k):ℂ) (P.radii (-k)) := by
    have hh := hclosed hw
    refine ⟨hh.1,?_⟩
    have hd := dist_neg_neg w (-(P.centers (-k):ℂ))
    simp only [neg_neg] at hd
    rw [mem_ball,hd]
    simpa only [mem_ball,Complex.ofReal_neg] using hh.2
  have hsphere := sourceCanonicalRootDomain_of_enclosingCircle (by norm_num) (by norm_num) (P.sourcePsi q) k c r hseg' (by
    intro w hw
    let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 k
      (P.centers k) (P.radii k) (P.radii_pos _) (P.discs_eq _)
    exact D.closedBall_subset_omittedDomain (ball_subset_closedBall (hclosed' w (closedBall_subset_closedBall hrρ.le hw)).1))
  have hgap := P.eventually_abelian_gap_subset_ball m q hq c r hseg' hsphere
  have hμq : P.physicalDirichletFrequency k q ∈ ball c r := hseg'
    (canonicalAuxiliaryPeriodOneRoots_mem_sourcePeriodicSegment_of_realType (by norm_num) (by norm_num)
      .dirichlet (P.sourcePsi q) hreal k)
  have hμ := (P.analytic_physicalDirichletFrequency k q hq).continuousAt.eventually (isOpen_ball.mem_nhds hμq)
  obtain ⟨U,hUsub,hU,hqU⟩ := _root_.mem_nhds_iff.mp
    ((hgap.and hμ).and (P.physicalDirichletSource_open.mem_nhds (P.real_mem_physicalDirichletSource q hq hr)))
  exact ⟨c,r,ρ,hrpos,hrρ,hclosed',U,hU,hqU,(fun a ha => (hUsub ha).2),
    fun a ha => ⟨(hUsub ha).1.1,ball_subset_closedBall (hUsub ha).1.2⟩⟩

end NLS.KdV.HillProductEquationPatch
