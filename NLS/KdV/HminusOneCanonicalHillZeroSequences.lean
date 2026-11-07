import NLS.KdV.HillCommonZeroSequenceBalls

/-! ONE open connected complex neighborhood of the ENTIRE real native
Hminus-one form supports ALL full-l2 intrinsic Hill zero sequences.
The chart choice is before all numerator and retained-root indices. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusCanonicalZeroSequenceDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillHminusZeroSequenceBall, B.source

theorem isOpen_hillHminusCanonicalZeroSequenceDomain : IsOpen hillHminusCanonicalZeroSequenceDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem hillHminusCanonicalZeroSequenceDomain_subset_psiDomain :
    hillHminusCanonicalZeroSequenceDomain ⊆ hillHminusCanonicalPsiDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.subset hB

theorem real_mem_hillHminusCanonicalZeroSequenceDomain (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : q ∈ hillHminusCanonicalZeroSequenceDomain := by
  obtain ⟨B,_,hB⟩ := exists_hillHminusZeroSequenceBall q hq
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem isConnected_hillHminusCanonicalZeroSequenceDomain : IsConnected hillHminusCanonicalZeroSequenceDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillHminusZeroSequenceBall) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real (mem_ball_self B.radius_pos) (convex_ball B.center B.radius).isPreconnected
  have hcommon : (⋂ B : HillHminusZeroSequenceBall, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillHminusZeroSequenceBall, S ∪ B.source) = hillHminusCanonicalZeroSequenceDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusCanonicalZeroSequenceDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusCanonicalZeroSequenceDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

def hillHminusCanonicalZeroSequence (n : ℕ+) (q : PeriodOneHminusOne) : lp (fun _ : ℕ+ => ℂ) 2 :=
  if hq : q ∈ hillHminusCanonicalZeroSequenceDomain then
    (Classical.choose (mem_iUnion.mp hq)).value n q
  else 0

theorem HillHminusZeroSequenceBall.canonical_value_eq (B : HillHminusZeroSequenceBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) : hillHminusCanonicalZeroSequence n q = B.value n q := by
  have hdom : q ∈ hillHminusCanonicalZeroSequenceDomain := mem_iUnion.mpr ⟨B,hq⟩
  rw [hillHminusCanonicalZeroSequence,dif_pos hdom]
  let C : HillHminusZeroSequenceBall := Classical.choose (mem_iUnion.mp hdom)
  have hC : q ∈ C.source := Classical.choose_spec (mem_iUnion.mp hdom)
  exact C.value_eq_on_overlap B n ⟨hC,hq⟩

theorem analyticOnNhd_hillHminusCanonicalZeroSequence (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalZeroSequence n) hillHminusCanonicalZeroSequenceDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  apply (B.analytic_value n q hB).congr
  filter_upwards [B.source_open.mem_nhds hB] with a ha
  exact (B.canonical_value_eq n a ha).symm

theorem hillHminusCanonicalZeroSequence_real (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : hillHminusCanonicalZeroSequence n q = hillHminusPsiZeroDisplacement n ⟨q,hq⟩ := by
  obtain ⟨B,_,hB⟩ := exists_hillHminusZeroSequenceBall q hq
  rw [B.canonical_value_eq n q hB]
  exact B.real_eq n q hB hq

theorem hillHminusCanonicalZeroSequence_retained_root (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalZeroSequenceDomain) :
    hillHminusCanonicalPsi n (hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n q),q) = 0 := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  rw [B.canonical_value_eq n q hB]
  exact B.root n m hmn q hB

end NLS.KdV
