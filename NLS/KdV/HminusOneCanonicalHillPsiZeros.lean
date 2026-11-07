import NLS.KdV.HminusOneHillPsiZeroBalls

/-! For EACH retained index pair, the actual indexed real coefficient
extends to ONE open connected complex native H-minus-one neighborhood
of the ENTIRE real form. Its values are simple numerator zeros, and
all chart presentations agree on whole complex overlaps. The domain
may depend on the pair; a COMMON all-pair domain is still required. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusPsiZeroDomain (n m : ℕ+) : Set PeriodOneHminusOne :=
  ⋃ B : HillHminusPsiZeroBall n m, B.source

theorem isOpen_hillHminusPsiZeroDomain (n m : ℕ+) : IsOpen (hillHminusPsiZeroDomain n m) :=
  isOpen_iUnion (fun B => B.source_open)

theorem hillHminusPsiZeroDomain_subset (n m : ℕ+) :
    hillHminusPsiZeroDomain n m ⊆ hillHminusCanonicalPsiDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.subset hB

theorem real_mem_hillHminusPsiZeroDomain (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) : q ∈ hillHminusPsiZeroDomain n m := by
  obtain ⟨B,_,hB⟩ := exists_hillHminusPsiZeroBall q hr n m hmn
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem isConnected_hillHminusPsiZeroDomain (n m : ℕ+) (hmn : m ≠ n) :
    IsConnected (hillHminusPsiZeroDomain n m) := by
  let R : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hR : IsPreconnected R := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillHminusPsiZeroBall n m) : IsPreconnected (R ∪ B.source) :=
    hR.union B.center B.center_real (mem_ball_self B.radius_pos) (convex_ball B.center B.radius).isPreconnected
  have hcommon : (⋂ B : HillHminusPsiZeroBall n m, R ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillHminusPsiZeroBall n m, R ∪ B.source) = hillHminusPsiZeroDomain n m := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqR | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusPsiZeroDomain n m hmn q hqR
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusPsiZeroDomain n m hmn 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

def hillHminusCanonicalRetainedPsiZero (n m : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  if hq : q ∈ hillHminusPsiZeroDomain n m then
    (Classical.choose (mem_iUnion.mp hq)).value q
  else 0

theorem HillHminusPsiZeroBall.canonical_zero_eq {n m : ℕ+} (B : HillHminusPsiZeroBall n m)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    hillHminusCanonicalRetainedPsiZero n m q = B.value q := by
  have hdom : q ∈ hillHminusPsiZeroDomain n m := mem_iUnion.mpr ⟨B,hq⟩
  rw [hillHminusCanonicalRetainedPsiZero,dif_pos hdom]
  let C : HillHminusPsiZeroBall n m := Classical.choose (mem_iUnion.mp hdom)
  have hC : q ∈ C.source := Classical.choose_spec (mem_iUnion.mp hdom)
  exact C.value_eq_on_overlap B ⟨hC,hq⟩

theorem analyticOnNhd_hillHminusCanonicalRetainedPsiZero (n m : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalRetainedPsiZero n m) (hillHminusPsiZeroDomain n m) := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  apply (B.analytic_value q hB).congr
  filter_upwards [B.source_open.mem_nhds hB] with a ha
  exact (B.canonical_zero_eq a ha).symm

theorem hillHminusCanonicalRetainedPsiZero_eq_real (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    hillHminusCanonicalRetainedPsiZero n m q = (hillHminusCanonicalPsiRealZero n m q hr:ℂ) := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp (real_mem_hillHminusPsiZeroDomain n m hmn q hr)
  exact (B.canonical_zero_eq q hB).trans (B.real_eq q hB hr)

theorem hillHminusCanonicalRetainedPsiZero_is_simple_root (n m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusPsiZeroDomain n m) :
    hillHminusCanonicalPsi n (hillHminusCanonicalRetainedPsiZero n m q,q) = 0 ∧
      deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,q)) (hillHminusCanonicalRetainedPsiZero n m q) ≠ 0 := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  rw [B.canonical_zero_eq q hB]
  exact ⟨B.root q hB,B.simple q hB⟩

end NLS.KdV
