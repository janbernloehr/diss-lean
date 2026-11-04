import NLS.KdV.HillAbelianFrequencyDifferentials
import NLS.ComplexAnalysis.PrimitiveOnDiscComplement
import NLS.ComplexAnalysis.SegmentIsolatingCircles

/-! Actual off-index Hill Abelian primitives on the ENTIRE original
frequency gap disc minus its gap. The zero period is proved from the
exact Hill normalization, including complex and collapsed gaps. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def abelianGapDisc (P : HillProductEquationPatch) (m : ℕ+) (q : PeriodOneHminusOne) : Set ℂ :=
  ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) \ sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)

theorem analytic_abelianFrequencyDifferential_on_closed_cut_disc (P : HillProductEquationPatch)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)) :
    AnalyticOnNhd ℂ (fun z => P.abelianFrequencyDifferential n (z,q))
      (closedBall (D.center:ℂ) D.radius \ sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)) := by
  intro z hz
  have hroot : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi q) := by
    intro j
    by_cases hj : j = ((m:ℕ):ℤ)
    · subst j; exact hz.2
    · exact D.closedBall_subset_omittedDomain hz.1 j hj
  have hnum := (P.analytic_abelianFrequencyNumerator n (z,q) ⟨mem_univ _,hq⟩).comp
    (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  exact hnum.div (sourceCanonicalRoot_analyticOnNhd (by norm_num) (by norm_num) (P.sourcePsi q) z hroot)
    (sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) (P.sourcePsi q) z hroot)

theorem exists_offIndex_abelian_cutDisc_primitive (P : HillProductEquationPatch) (n m : ℕ+)
    (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball (D.center:ℂ) D.radius \ sourcePeriodicSegment
      (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ),
      HasDerivAt F (P.abelianFrequencyDifferential n (z,q)) z := by
  obtain ⟨r,s,hr,hrs,hsR,hgap⟩ := exists_nested_radii_of_segment_subset_ball _ _ (D.center:ℂ) D.radius D.gap
  have hrR : r < D.radius := hrs.trans hsR
  let C : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) := {
    center := D.center
    radius := r
    radius_pos := hr
    gap := hgap
    other := by
      intro j hj w hw
      rcases D.other j hj w hw with hl | hu
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith) }
  have hzero : (∮ z in C((D.center:ℂ),r), P.abelianFrequencyDifferential n (z,q)) = 0 := by
    have hp := P.abelianFrequencyDifferential_period n m q hq C
    rw [if_neg hmn] at hp
    exact (mul_eq_zero.mp hp).resolve_left (inv_ne_zero (by simp [Real.pi_ne_zero]))
  have hclosed : IsClosed (sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)) := by
    apply IsCompact.isClosed
    change IsCompact (segment ℝ _ _)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hmid := sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)
  exact exists_primitive_on_disc_complement_of_zero_period _ (D.center:ℂ)
    (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)) r D.radius hr hrR
    _ hclosed hmid ((convex_segment _ _).starConvex hmid) hgap
    (P.analytic_abelianFrequencyDifferential_on_closed_cut_disc n m q hq D) hzero

theorem exists_offIndex_abelianGapDisc_primitive (P : HillProductEquationPatch) (n m : ℕ+)
    (hmn : m ≠ n) (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    ∃ F : ℂ → ℂ, ∀ z ∈ P.abelianGapDisc m q, HasDerivAt F (P.abelianFrequencyDifferential n (z,q)) z := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  exact P.exists_offIndex_abelian_cutDisc_primitive n m hmn q hq D

end NLS.KdV.HillProductEquationPatch
