import NLS.KdV.HillOffIndexAbsoluteSummability
import NLS.KdV.HillProductEquationFamilyFactory
import NLS.KdV.HillCanonicalPhysicalAbelianValue
import NLS.KdV.HillOffIndexRealAbelianValue

/-! The infinite ACTUAL off-index correction is absolutely convergent
on ONE OPEN native complex neighborhood of the ENTIRE real form,
chosen BEFORE ALL n. Analyticity and uniform all-n bounds are separate. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusOffIndexAbelianTerm (n : ℕ+) (q : PeriodOneHminusOne) (m : ℕ+) : ℂ :=
  if m = n then 0 else hillHminusPhysicalOffIndexAbelianValue n m q

structure HillAbelianSummabilityNeighborhood where
  source : Set PeriodOneHminusOne
  source_open : IsOpen source
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  center_mem : center ∈ source
  source_preconnected : IsPreconnected source
  subset : source ⊆ hillHminusPhysicalAbelianDomain
  summable : ∀ n : ℕ+, ∀ q ∈ source, Summable (fun m => ‖hillHminusOffIndexAbelianTerm n q m‖)

theorem exists_hillAbelianSummabilityNeighborhood_of_real (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : ∃ B : HillAbelianSummabilityNeighborhood, q ∈ B.source := by
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hq,_,hA⟩ := exists_hillProductEquationPatch_with_family A q hr
  have HP : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hA]; exact H
  obtain ⟨U,hU,hqU,_,hsum⟩ := P.exists_open_physicalOffIndex_absolute_summability HP q
    (P.real_mem_physicalDirichletSource q hq hr)
  obtain ⟨r,hrpos,hball,heq⟩ := exists_common_canonical_physical_Abelian_patch_ball P q hq hr
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp
    ((hU.inter isOpen_ball).mem_nhds (show q ∈ U ∩ ball q r from ⟨hqU,mem_ball_self hrpos⟩))
  refine ⟨⟨ball q δ,isOpen_ball,q,hr,mem_ball_self hδ,(convex_ball q δ).isPreconnected,
    (fun a ha => (hball (hδsub ha).2).2),?_⟩,mem_ball_self hδ⟩
  intro n a ha
  have haU := hδsub ha
  apply (hsum n a haU.1).congr
  intro m
  by_cases hmn : m = n
  · simp only [hillHminusOffIndexAbelianTerm,if_pos hmn]
  · rw [hillHminusOffIndexAbelianTerm,if_neg hmn,if_neg hmn,heq n m hmn a haU.2]

def hillHminusOffIndexSummabilityDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillAbelianSummabilityNeighborhood, B.source

theorem isOpen_hillHminusOffIndexSummabilityDomain : IsOpen hillHminusOffIndexSummabilityDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem real_mem_hillHminusOffIndexSummabilityDomain (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : q ∈ hillHminusOffIndexSummabilityDomain := by
  obtain ⟨B,hB⟩ := exists_hillAbelianSummabilityNeighborhood_of_real q hr
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem isConnected_hillHminusOffIndexSummabilityDomain : IsConnected hillHminusOffIndexSummabilityDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillAbelianSummabilityNeighborhood) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real B.center_mem B.source_preconnected
  have hcommon : (⋂ B : HillAbelianSummabilityNeighborhood, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillAbelianSummabilityNeighborhood, S ∪ B.source) = hillHminusOffIndexSummabilityDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusOffIndexSummabilityDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusOffIndexSummabilityDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

theorem hillHminusOffIndexSummabilityDomain_subset :
    hillHminusOffIndexSummabilityDomain ⊆ hillHminusPhysicalAbelianDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.subset hB

theorem summable_norm_hillHminusOffIndexAbelianTerm (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexSummabilityDomain) :
    Summable (fun m => ‖hillHminusOffIndexAbelianTerm n q m‖) := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.summable n q hB

def hillHminusOffIndexAbelianCorrection (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  ∑' m : ℕ+, hillHminusOffIndexAbelianTerm n q m

theorem hillHminusOffIndexAbelianCorrection_hasSum (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexSummabilityDomain) :
    HasSum (hillHminusOffIndexAbelianTerm n q) (hillHminusOffIndexAbelianCorrection n q) :=
  (summable_norm_hillHminusOffIndexAbelianTerm n q hq).of_norm.hasSum

theorem hillHminusOffIndexAbelianCorrection_im_eq_zero_of_real (n : ℕ+)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    (hillHminusOffIndexAbelianCorrection n q).im = 0 := by
  rw [hillHminusOffIndexAbelianCorrection,Complex.im_tsum
    (summable_norm_hillHminusOffIndexAbelianTerm n q (real_mem_hillHminusOffIndexSummabilityDomain q hr)).of_norm]
  have hz (m : ℕ+) : (hillHminusOffIndexAbelianTerm n q m).im = 0 := by
    by_cases hmn : m = n
    · simp only [hillHminusOffIndexAbelianTerm,if_pos hmn,zero_im]
    · simpa only [hillHminusOffIndexAbelianTerm,if_neg hmn] using
        hillHminusPhysicalOffIndexAbelianValue_im_eq_zero_of_real n m hmn q hr
  simp only [hz,tsum_zero]

end NLS.KdV
