import NLS.KdV.HillHminusIntrinsicDeflatedRoot
import NLS.KdV.HillHminusOriginalDirichletSheetGerm
import NLS.KdV.HillDeflatedGapPhysicalMatching
import NLS.KdV.HillOwnGapFactor

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- The ORIGINAL own-gap Cartesian factor, with its actual signed
Dirichlet sheet, has a genuine analytic H-minus-one germ at EVERY
original source and positive index, INCLUDING collapsed own gaps. -/
theorem exists_hillOriginal_ownGapFactor_hminus_physical_germ
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    ∃ F : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ F (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        F (hillOriginalHminusSource p.val) = hillOwnGapFactor p.val p.property.1 p.property.2 n n.pos := by
  obtain ⟨a,S,ha,hS,ha0,_,hM⟩ := exists_hillOriginal_dirichlet_sheet_hminus_physical_germ q n
  obtain ⟨U,_,hqU,hMid,_,_⟩ := exists_hillHminusIntrinsicGapSymmetricData_analytic_neighborhood
    q.val q.property.1 q.property.2 n n.pos
  have hμbase : (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos : ℂ) ∈
      segment ℝ (hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ)-1) : ℂ)
        (hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ)) : ℂ) :=
    NLS.ComplexAnalysis.ofReal_mem_ordered_segment _ _ _
      (monotone_hillRealLabels q.val q.property.1 q.property.2 (by omega))
      (hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 n n.pos)
  have hdom : (a (hillOriginalHminusSource q.val),hillOriginalHminusSource q.val) ∈
      hillHminusIntrinsicDeflatedRootDomain q.val q.property.1 q.property.2 n := by
    rw [ha0]
    exact mem_hillHminusIntrinsicDeflatedRootDomain_base q.val q.property.1 q.property.2 n n.pos _
      (hillRealGapSegment_subset_intrinsic_contour_ball q.val q.property.1 q.property.2 n n.pos hμbase)
  let B : PeriodOneHminusOne → ℂ := fun b =>
    hillHminusIntrinsicDeflatedRoot q.val q.property.1 q.property.2 n (a b,b)
  have hB : AnalyticAt ℂ B (hillOriginalHminusSource q.val) :=
    (analyticOnNhd_hillHminusIntrinsicDeflatedRoot q.val q.property.1 q.property.2 n n.pos _ hdom).comp
      (f := fun b : PeriodOneHminusOne => (a b,b)) (ha.prod analyticAt_id)
  have hBn : B (hillOriginalHminusSource q.val) ≠ 0 :=
    hillHminusIntrinsicDeflatedRoot_ne_zero q.val q.property.1 q.property.2 n n.pos _ hdom
  let F : PeriodOneHminusOne → ℂ := fun b =>
    hillHminusIntrinsicGapMidpoint q.val q.property.1 q.property.2 n b - a b + S b/B b
  refine ⟨F,((hMid _ hqU).sub ha).add (hS.div hB hBn),?_⟩
  obtain ⟨E,V,hE,hV,hgapE,hqV,hrootmatch⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching
    q.val q.property.1 q.property.2 n n.pos
  obtain ⟨W,hW,hqW,hmidmatch⟩ := exists_hillHminusIntrinsicGapSymmetricData_physical_neighborhood
    q.val q.property.1 q.property.2 n n.pos
  have hμE : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q, a (hillOriginalHminusSource p.val) ∈ E := by
    have hc : ContinuousAt (fun p : RealPeriodOneHillPotential => a (hillOriginalHminusSource p.val)) q :=
      ha.continuousAt.comp (f := fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
        (hillOriginalHminusSource.continuous.comp continuous_subtype_val).continuousAt
    apply hc.preimage_mem_nhds (hE.mem_nhds ?_)
    rw [ha0]
    exact hgapE hμbase
  filter_upwards [hM,hμE,hV.mem_nhds hqV,hW.mem_nhds hqW] with p hp hpE hpV hpW
  have hroot : B (hillOriginalHminusSource p.val) =
      hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 n (a (hillOriginalHminusSource p.val)) := by
    dsimp only [B]
    rw [hillHminusIntrinsicDeflatedRoot_original_source q.val q.property.1 q.property.2 n p.val p.property.1]
    exact (hrootmatch p hpV _ hpE).2.2
  dsimp only [F]
  rw [(hmidmatch p hpW).1,hroot,hp.1,hp.2]
  rfl

end NLS.KdV
