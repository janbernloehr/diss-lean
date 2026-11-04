import NLS.KdV.HillEnergyRootBoxes

/-! A canonical ACTUAL Hill energy sheet on one OPEN JOINT energy/source
domain. The chart choice precedes ALL numerator indices, roots agree on
WHOLE complex overlaps, and every available local sheet value at a REAL
source is included, in particular EVERY nonreal energy. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusCanonicalEnergyRootDomain : Set (ℂ × PeriodOneHminusOne) :=
  ⋃ B : HillHminusEnergyRootBox, B.domain

theorem isOpen_hillHminusCanonicalEnergyRootDomain : IsOpen hillHminusCanonicalEnergyRootDomain :=
  isOpen_iUnion (fun B => B.domain_open)

theorem hillHminusCanonicalEnergyRootDomain_subset_simpleSource :
    hillHminusCanonicalEnergyRootDomain ⊆ univ ×ˢ hillHminusSimpleZeroSequenceDomain := by
  intro t ht
  obtain ⟨B,hB⟩ := mem_iUnion.mp ht
  exact ⟨mem_univ _,B.source_subset hB.2⟩

def hillHminusCanonicalEnergyRoot (t : ℂ × PeriodOneHminusOne) : ℂ :=
  if ht : t ∈ hillHminusCanonicalEnergyRootDomain then
    (Classical.choose (mem_iUnion.mp ht)).root t
  else 0

theorem HillHminusEnergyRootBox.canonical_root_eq (B : HillHminusEnergyRootBox)
    (t : ℂ × PeriodOneHminusOne) (ht : t ∈ B.domain) : hillHminusCanonicalEnergyRoot t = B.root t := by
  have hdom : t ∈ hillHminusCanonicalEnergyRootDomain := mem_iUnion.mpr ⟨B,ht⟩
  rw [hillHminusCanonicalEnergyRoot,dif_pos hdom]
  let C : HillHminusEnergyRootBox := Classical.choose (mem_iUnion.mp hdom)
  have hC : t ∈ C.domain := Classical.choose_spec (mem_iUnion.mp hdom)
  exact C.root_eq_on_overlap B ⟨hC,ht⟩

theorem analyticOnNhd_hillHminusCanonicalEnergyRoot :
    AnalyticOnNhd ℂ hillHminusCanonicalEnergyRoot hillHminusCanonicalEnergyRootDomain := by
  intro t ht
  obtain ⟨B,hB⟩ := mem_iUnion.mp ht
  apply (B.analytic_root t hB).congr
  filter_upwards [B.domain_open.mem_nhds hB] with s hs
  exact (B.canonical_root_eq s hs).symm

theorem hillHminusCanonicalEnergyRoot_ne_zero (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ hillHminusCanonicalEnergyRootDomain) : hillHminusCanonicalEnergyRoot t ≠ 0 := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp ht
  rw [B.canonical_root_eq t hB]
  exact B.root_ne_zero t hB

theorem hillHminusCanonicalEnergyRoot_sq (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ hillHminusCanonicalEnergyRootDomain) : hillHminusCanonicalEnergyRoot t^2 = hillHminusRadicand t.2 t.1 := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp ht
  rw [B.canonical_root_eq t hB]
  exact B.root_sq t hB

theorem real_mem_hillHminusCanonicalEnergyRootDomain_of_local
    (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) (E : ℂ) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (ht : (E,q) ∈ B.energyDomain A) :
    (E,q) ∈ hillHminusCanonicalEnergyRootDomain := by
  obtain ⟨C,_,_,_,_,hC⟩ := exists_hillHminusEnergyRootBox_of_real_mem B A E q hr ht
  exact mem_iUnion.mpr ⟨C,hC⟩

theorem hillHminusCanonicalEnergyRoot_eq_local_of_real
    (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) (E : ℂ) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (ht : (E,q) ∈ B.energyDomain A) :
    hillHminusCanonicalEnergyRoot (E,q) = B.energyRoot (E,q) := by
  obtain ⟨C,hparent,_,_,_,hC⟩ := exists_hillHminusEnergyRootBox_of_real_mem B A E q hr ht
  rw [C.canonical_root_eq (E,q) hC]
  change C.parent.energyRoot (E,q) = B.energyRoot (E,q)
  rw [hparent]

theorem nonreal_mem_hillHminusCanonicalEnergyRootDomain (E : ℂ) (hE : E.im ≠ 0)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) : (E,q) ∈ hillHminusCanonicalEnergyRootDomain := by
  obtain ⟨A⟩ := nonempty_miuraHillPsiFamily
  obtain ⟨B,hB⟩ := exists_local_hminusHillPsiFamily A q hr
  exact real_mem_hillHminusCanonicalEnergyRootDomain_of_local B A E q hr (B.nonreal_energy_mem_domain A q hB hr E hE)

theorem hillHminusCanonicalEnergyRoot_eq_physical_of_real (E : ℂ) (hE : E.im ≠ 0)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    hillHminusCanonicalEnergyRoot (E,q) = hillHminusContinuedRoot (E,q) := by
  obtain ⟨A⟩ := nonempty_miuraHillPsiFamily
  obtain ⟨B,hB⟩ := exists_local_hminusHillPsiFamily A q hr
  rw [hillHminusCanonicalEnergyRoot_eq_local_of_real B A E q hr (B.nonreal_energy_mem_domain A q hB hr E hE)]
  exact B.energyRoot_eq_physical_of_real q hB.1 hr E hE

def hillHminusEnergySheetSource : Set PeriodOneHminusOne := ⋃ B : HillHminusEnergyRootBox, B.source

theorem isOpen_hillHminusEnergySheetSource : IsOpen hillHminusEnergySheetSource :=
  isOpen_iUnion (fun _ => isOpen_ball)

theorem hillHminusEnergySheetSource_subset_simpleDomain :
    hillHminusEnergySheetSource ⊆ hillHminusSimpleZeroSequenceDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.source_subset hB

theorem real_mem_hillHminusEnergySheetSource (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    q ∈ hillHminusEnergySheetSource := by
  have hroot := nonreal_mem_hillHminusCanonicalEnergyRootDomain I (by simp) q hr
  obtain ⟨B,hB⟩ := mem_iUnion.mp hroot
  exact mem_iUnion.mpr ⟨B,hB.2⟩

theorem isConnected_hillHminusEnergySheetSource : IsConnected hillHminusEnergySheetSource := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillHminusEnergyRootBox) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real (mem_ball_self B.radius_pos) (convex_ball B.center B.radius).isPreconnected
  have hcommon : (⋂ B : HillHminusEnergyRootBox, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillHminusEnergyRootBox, S ∪ B.source) = hillHminusEnergySheetSource := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusEnergySheetSource q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusEnergySheetSource 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

theorem hillHminusCanonicalEnergyRootDomain_subset_sheetSource :
    hillHminusCanonicalEnergyRootDomain ⊆ univ ×ˢ hillHminusEnergySheetSource := by
  intro t ht
  obtain ⟨B,hB⟩ := mem_iUnion.mp ht
  exact ⟨mem_univ _,mem_iUnion.mpr ⟨B,hB.2⟩⟩

end NLS.KdV
