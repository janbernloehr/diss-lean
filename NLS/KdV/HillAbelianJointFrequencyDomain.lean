import NLS.KdV.HillOffIndexAbelianEndpointIntegrals
import NLS.ComplexAnalysis.ConnectedSetInBall

/-! Joint analyticity of the ACTUAL frequency forms on the unchanged
native product patch. Its existing omitted-root data also make ALL
filled gap numerators jointly analytic across their whole closed discs. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def abelianJointFrequencyDomain (P : HillProductEquationPatch) : Set (ℂ × PeriodOneHminusOne) :=
  {t | t.2 ∈ P.source ∧ t.1 ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi t.2)}

theorem abelianJointFrequencyDomain_open (P : HillProductEquationPatch) : IsOpen P.abelianJointFrequencyDomain := by
  let T : ℂ × PeriodOneHminusOne → ℂ × CoeffPair 2 := fun t => (t.1,P.sourcePsi t.2)
  have hT : AnalyticOnNhd ℂ T (univ ×ˢ P.source) := by
    intro t ht
    exact analyticAt_fst.prod ((P.analytic_sourcePsi t.2 ht.2).comp (f := Prod.snd) analyticAt_snd)
  have hopen : IsOpen (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) P.W) := by
    rw [sourceCanonicalRootJointDomain_eq_inter_omitted]
    exact ((P.quotients.roots.joint 0).1).inter ((P.quotients.roots.joint 1).1)
  have he : P.abelianJointFrequencyDomain = (univ ×ˢ P.source) ∩ T ⁻¹' sourceCanonicalRootJointDomain (by norm_num) (by norm_num) P.W := by
    ext t
    exact ⟨fun ht => ⟨⟨mem_univ _,ht.1⟩,(P.image _ ht.1).1,ht.2⟩,fun ht => ⟨ht.1.2,ht.2.2⟩⟩
  rw [he]
  exact hT.continuousOn.isOpen_inter_preimage (isOpen_univ.prod P.source_open) hopen

theorem analytic_abelianSelectedRoot (P : HillProductEquationPatch) (m : ℕ+) :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne =>
      sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1)
      {t | t.2 ∈ P.source ∧ t.1 ∉ sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi t.2) ((m:ℕ):ℤ)} := by
  intro t ht
  exact ((P.quotients.roots.roots.symmetric.standardRoot_joint ((m:ℕ):ℤ)) (t.1,P.sourcePsi t.2)
    ⟨(P.image _ ht.1).1,ht.2⟩).comp
    (f := fun s : ℂ × PeriodOneHminusOne => (s.1,P.sourcePsi s.2))
    (analyticAt_fst.prod ((P.analytic_sourcePsi t.2 ht.1).comp (f := Prod.snd) analyticAt_snd))

theorem analytic_abelianFrequencyRoot (P : HillProductEquationPatch) :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne =>
      sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi t.2) t.1) P.abelianJointFrequencyDomain := by
  intro t ht
  have hψ := (P.image _ ht.1).1
  have hQ := P.quotients.roots.roots.symmetric.standardRoot_joint 0 (t.1,P.sourcePsi t.2) ⟨hψ,ht.2 0⟩
  have hO := (P.quotients.roots.joint 0).2 (t.1,P.sourcePsi t.2) ⟨hψ,fun j _ => ht.2 j⟩
  have hF : AnalyticAt ℂ (fun x : ℂ × CoeffPair 2 => 2*I*
      sourceStandardRoot (by norm_num) (by norm_num) x.2 0 x.1*
      sourceStandardRootOmittedJointProduct (by norm_num) (by norm_num) 0 x) (t.1,P.sourcePsi t.2) :=
    (analyticAt_const.mul hQ).mul hO
  have ha := hF.comp
    (f := fun s : ℂ × PeriodOneHminusOne => (s.1,P.sourcePsi s.2))
    (analyticAt_fst.prod ((P.analytic_sourcePsi t.2 ht.1).comp (f := Prod.snd) analyticAt_snd))
  apply ha.congr
  exact Filter.Eventually.of_forall (fun s => (sourceCanonicalRoot_eq_omitted (by norm_num) (by norm_num) 0 (P.sourcePsi s.2) s.1).symm)

theorem analytic_abelianFrequencyDifferential_joint (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.abelianFrequencyDifferential n) P.abelianJointFrequencyDomain := by
  intro t ht
  exact (P.analytic_abelianFrequencyNumerator n t ⟨mem_univ _,ht.1⟩).div
    (P.analytic_abelianFrequencyRoot t ht)
    (sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) (P.sourcePsi t.2) t.1 ht.2)

theorem analytic_abelianGapNumerator_on_patch (P : HillProductEquationPatch) (n m : ℕ+) :
    AnalyticOnNhd ℂ (P.abelianGapNumerator n m)
      (closedBall (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source) := by
  intro t ht
  let D := P.isolating.periodCircle (P.sourcePsi t.2) (P.image t.2 ht.2).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hz := D.closedBall_subset_omittedDomain ht.1
  have hprod := ((P.quotients.roots.joint ((m:ℕ):ℤ)).2 (t.1,P.sourcePsi t.2) ⟨(P.image _ ht.2).1,hz⟩).comp
    (f := fun x : ℂ × PeriodOneHminusOne => (x.1,P.sourcePsi x.2))
    (analyticAt_fst.prod ((P.analytic_sourcePsi t.2 ht.2).comp (f := Prod.snd) analyticAt_snd))
  exact (P.analytic_abelianFrequencyNumerator n t ⟨mem_univ _,ht.2⟩).div
    ((analyticAt_const.mul analyticAt_const).mul hprod)
    (mul_ne_zero (by simp) (sourceStandardRootOmittedProduct_ne_zero (by norm_num) (by norm_num)
      (P.sourcePsi t.2) t.1 ((m:ℕ):ℤ) hz))

theorem analytic_abelianGapMidpoint (P : HillProductEquationPatch) (m : ℕ+) :
    AnalyticOnNhd ℂ (fun y : PeriodOneHminusOne => sourceStandardRootMidpoint
      (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)) P.source := by
  intro q hq
  exact (P.quotients.roots.roots.symmetric.midpoint ((m:ℕ):ℤ) (P.sourcePsi q) (P.image q hq).1).comp
    (f := P.sourcePsi) (P.analytic_sourcePsi q hq)

theorem eventually_abelian_gap_subset_ball (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (c : ℂ) (r : ℝ)
    (hseg : sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) ⊆ ball c r)
    (hsphere : sphere c r ⊆ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi q)) :
    ∀ᶠ y in 𝓝 q, sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ) ⊆ ball c r := by
  have hslice : sphere c r ×ˢ ({q} : Set PeriodOneHminusOne) ⊆ P.abelianJointFrequencyDomain := by
    rintro ⟨z,y⟩ ⟨hz,hy⟩
    have : y = q := hy
    subst y
    exact ⟨hq,hsphere hz⟩
  obtain ⟨A,U,_,hU,hA,hqU,hAU⟩ := generalized_tube_lemma (isCompact_sphere c r) isCompact_singleton P.abelianJointFrequencyDomain_open hslice
  have hm := P.analytic_abelianGapMidpoint m q hq
  have hev : ∀ᶠ y in 𝓝 q, sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ) ∈ ball c r :=
    hm.continuousAt (isOpen_ball.mem_nhds (hseg (sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))))
  filter_upwards [hU.mem_nhds (hqU (mem_singleton q)),hev] with y hy hmid
  apply subset_ball_of_isPreconnected_of_disjoint_sphere (convex_segment _ _).isPreconnected c r
  · apply Set.disjoint_left.mpr
    intro z hz hzS
    have hzp : (z,y) ∈ P.abelianJointFrequencyDomain :=
      hAU (show (z,y) ∈ A ×ˢ U from ⟨hA hzS,hy⟩)
    have hnot : z ∉ sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ) := hzp.2 ((m:ℕ):ℤ)
    exact hnot hz
  · exact ⟨_,sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ),hmid⟩

end NLS.KdV.HillProductEquationPatch
