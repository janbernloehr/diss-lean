import NLS.KdV.HillCanonicalOffIndexPartialSums
import NLS.KdV.HillOffIndexAnalyticCorrection

/-! A common complex domain for the actual analytic infinite correction.
Every certificate has locally uniform convergence BEFORE ALL n, and is
constructed at every real native source using the retained actual data. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

structure HillAbelianAnalyticNeighborhood extends HillAbelianSummabilityNeighborhood where
  locally_uniform : ∀ q ∈ source, ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ source ∧
    ∀ n : ℕ+, TendstoUniformlyOn (hillHminusOffIndexAbelianPartialSum n)
      (hillHminusOffIndexAbelianCorrection n) atTop U

theorem exists_hillAbelianAnalyticNeighborhood_of_real (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : ∃ B : HillAbelianAnalyticNeighborhood, q ∈ B.source := by
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hq,_,hA⟩ := exists_hillProductEquationPatch_with_family A q hr
  have HP : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hA]; exact H
  obtain ⟨r,hrpos,hball,heq⟩ := exists_common_offIndex_correction_patch_ball P q hq hr
  let B : HillAbelianSummabilityNeighborhood := {
    source := ball q r
    source_open := isOpen_ball
    center := q
    center_real := hr
    center_mem := mem_ball_self hrpos
    source_preconnected := (convex_ball q r).isPreconnected
    subset := fun a ha => (hball ha).2
    summable := by
      intro n a ha
      obtain ⟨U,_,haU,_,hsum⟩ := P.exists_open_physicalOffIndex_absolute_summability HP a (hball ha).1
      apply (hsum n a haU).congr
      intro m
      exact congrArg (fun f : ℕ+ → ℂ => ‖f m‖) (heq n a ha).1.symm }
  refine ⟨⟨B,?_⟩,mem_ball_self hrpos⟩
  intro a ha
  obtain ⟨U,hU,haU,_,hconv⟩ := P.exists_local_uniform_physicalOffIndexAbelianCorrection HP a (hball ha).1
  refine ⟨U ∩ ball q r,hU.inter isOpen_ball,⟨haU,ha⟩,inter_subset_right,?_⟩
  intro n
  have hc := (hconv n).mono (inter_subset_left : U ∩ ball q r ⊆ U)
  apply (hc.congr (Eventually.of_forall (fun N b hb => (heq n b hb.2).2.1 N |>.symm))).congr_right
  intro b hb
  exact (heq n b hb.2).2.2.symm

def hillHminusOffIndexAnalyticDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillAbelianAnalyticNeighborhood, B.source

theorem isOpen_hillHminusOffIndexAnalyticDomain : IsOpen hillHminusOffIndexAnalyticDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem real_mem_hillHminusOffIndexAnalyticDomain (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : q ∈ hillHminusOffIndexAnalyticDomain := by
  obtain ⟨B,hB⟩ := exists_hillAbelianAnalyticNeighborhood_of_real q hr
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem hillHminusOffIndexAnalyticDomain_subset_summability :
    hillHminusOffIndexAnalyticDomain ⊆ hillHminusOffIndexSummabilityDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact mem_iUnion.mpr ⟨B.toHillAbelianSummabilityNeighborhood,hB⟩

theorem hillHminusOffIndexAnalyticDomain_subset_physical :
    hillHminusOffIndexAnalyticDomain ⊆ hillHminusPhysicalAbelianDomain :=
  hillHminusOffIndexAnalyticDomain_subset_summability.trans hillHminusOffIndexSummabilityDomain_subset

theorem exists_locally_uniform_hillHminusOffIndexAbelianCorrection (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexAnalyticDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusOffIndexAnalyticDomain ∧
      ∀ n : ℕ+, TendstoUniformlyOn (hillHminusOffIndexAbelianPartialSum n)
        (hillHminusOffIndexAbelianCorrection n) atTop U := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  obtain ⟨U,hU,hqU,hUB,hconv⟩ := B.locally_uniform q hB
  exact ⟨U,hU,hqU,(fun a ha => mem_iUnion.mpr ⟨B,hUB ha⟩),hconv⟩

theorem isConnected_hillHminusOffIndexAnalyticDomain : IsConnected hillHminusOffIndexAnalyticDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillAbelianAnalyticNeighborhood) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real B.center_mem B.source_preconnected
  have hcommon : (⋂ B : HillAbelianAnalyticNeighborhood, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillAbelianAnalyticNeighborhood, S ∪ B.source) = hillHminusOffIndexAnalyticDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusOffIndexAnalyticDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusOffIndexAnalyticDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

end NLS.KdV
