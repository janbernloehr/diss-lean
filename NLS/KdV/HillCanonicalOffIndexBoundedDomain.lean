import NLS.KdV.HillCanonicalOffIndexAnalyticCorrection
import NLS.KdV.HillOffIndexUniformCorrectionBound

/-! ONE common open connected complex neighborhood of the entire real
native source form where the ACTUAL analytic infinite correction is
locally bounded UNIFORMLY in ALL n. Absolute sums obey the same bound. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

structure HillAbelianBoundedNeighborhood extends HillAbelianAnalyticNeighborhood where
  bound : ℝ
  bound_pos : 0 < bound
  absolute_bound : ∀ q ∈ source, ∀ n : ℕ+, (∑' m : ℕ+, ‖hillHminusOffIndexAbelianTerm n q m‖) ≤ bound

theorem exists_hillAbelianBoundedNeighborhood_of_real (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : ∃ B : HillAbelianBoundedNeighborhood, q ∈ B.source := by
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hq,_,hA⟩ := exists_hillProductEquationPatch_with_family A q hr
  have HP : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hA]; exact H
  obtain ⟨U,hU,hqU,_,R,hR,hbound⟩ := P.exists_local_uniform_physicalOffIndexAbelianCorrection_bound HP q hq hr
  obtain ⟨r,hrpos,hball,heq⟩ := exists_common_offIndex_correction_patch_ball P q hq hr
  have hqW := real_mem_hillHminusOffIndexAnalyticDomain q hr
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp
    (((hU.inter isOpen_ball).inter isOpen_hillHminusOffIndexAnalyticDomain).mem_nhds
      ⟨⟨hqU,mem_ball_self hrpos⟩,hqW⟩)
  let B : HillAbelianSummabilityNeighborhood := {
    source := ball q δ
    source_open := isOpen_ball
    center := q
    center_real := hr
    center_mem := mem_ball_self hδ
    source_preconnected := (convex_ball q δ).isPreconnected
    subset := fun a ha => hillHminusOffIndexAnalyticDomain_subset_physical (hδsub ha).2
    summable := fun n a ha => summable_norm_hillHminusOffIndexAbelianTerm n a
      (hillHminusOffIndexAnalyticDomain_subset_summability (hδsub ha).2) }
  let E : HillAbelianAnalyticNeighborhood := {
    toHillAbelianSummabilityNeighborhood := B
    locally_uniform := by
      intro a ha
      obtain ⟨V,hV,haV,_,hconv⟩ := exists_locally_uniform_hillHminusOffIndexAbelianCorrection a (hδsub ha).2
      exact ⟨V ∩ ball q δ,hV.inter isOpen_ball,⟨haV,ha⟩,inter_subset_right,
        fun n => (hconv n).mono inter_subset_left⟩ }
  refine ⟨⟨E,R,hR,?_⟩,mem_ball_self hδ⟩
  intro a ha n
  have ht := (heq n a (hδsub ha).1.2).1
  have hab := (hbound a (hδsub ha).1.1 n).1
  change (∑' m : ℕ+, ‖hillHminusOffIndexAbelianTerm n a m‖) ≤ R
  rw [ht]
  exact hab

def hillHminusOffIndexBoundedDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillAbelianBoundedNeighborhood, B.source

theorem isOpen_hillHminusOffIndexBoundedDomain : IsOpen hillHminusOffIndexBoundedDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem real_mem_hillHminusOffIndexBoundedDomain (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : q ∈ hillHminusOffIndexBoundedDomain := by
  obtain ⟨B,hB⟩ := exists_hillAbelianBoundedNeighborhood_of_real q hr
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem hillHminusOffIndexBoundedDomain_subset_analytic :
    hillHminusOffIndexBoundedDomain ⊆ hillHminusOffIndexAnalyticDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact mem_iUnion.mpr ⟨B.toHillAbelianAnalyticNeighborhood,hB⟩

theorem exists_locally_uniform_hillHminusOffIndexAbelianCorrection_bound (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexBoundedDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusOffIndexBoundedDomain ∧
      ∃ R : ℝ, 0 < R ∧ ∀ a ∈ U, ∀ n : ℕ+,
        (∑' m : ℕ+, ‖hillHminusOffIndexAbelianTerm n a m‖) ≤ R ∧
          ‖hillHminusOffIndexAbelianCorrection n a‖ ≤ R := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  refine ⟨B.source,B.source_open,hB,(fun a ha => mem_iUnion.mpr ⟨B,ha⟩),B.bound,B.bound_pos,?_⟩
  intro a ha n
  have hb := B.absolute_bound a ha n
  have hs := B.summable n a ha
  exact ⟨hb,(norm_tsum_le_tsum_norm hs).trans hb⟩

theorem isConnected_hillHminusOffIndexBoundedDomain : IsConnected hillHminusOffIndexBoundedDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillAbelianBoundedNeighborhood) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real B.center_mem B.source_preconnected
  have hcommon : (⋂ B : HillAbelianBoundedNeighborhood, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillAbelianBoundedNeighborhood, S ∪ B.source) = hillHminusOffIndexBoundedDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusOffIndexBoundedDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusOffIndexBoundedDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

end NLS.KdV
