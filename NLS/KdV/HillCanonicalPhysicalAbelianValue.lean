import NLS.KdV.HillPhysicalAbelianSourceBalls

/-! Intrinsic physical off-index Abelian divisor values on ONE OPEN
connected native complex source neighborhood of the ENTIRE real form.
The domain and all gluing choices precede ALL indices. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusPhysicalAbelianDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillPhysicalAbelianSourceBall, B.source

theorem isOpen_hillHminusPhysicalAbelianDomain : IsOpen hillHminusPhysicalAbelianDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem real_mem_hillHminusPhysicalAbelianDomain (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    q ∈ hillHminusPhysicalAbelianDomain := by
  obtain ⟨B,_,hq⟩ := exists_hillPhysicalAbelianSourceBall q hr
  exact mem_iUnion.mpr ⟨B,hq⟩

def hillHminusPhysicalOffIndexAbelianValue (n m : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  if hq : q ∈ hillHminusPhysicalAbelianDomain then
    (Classical.choose (mem_iUnion.mp hq)).value n m q
  else 0

namespace HillPhysicalAbelianSourceBall

theorem canonical_value_eq (B : HillPhysicalAbelianSourceBall) (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    hillHminusPhysicalOffIndexAbelianValue n m q = B.value n m q := by
  have hdom : q ∈ hillHminusPhysicalAbelianDomain := mem_iUnion.mpr ⟨B,hq⟩
  rw [hillHminusPhysicalOffIndexAbelianValue,dif_pos hdom]
  let C := Classical.choose (mem_iUnion.mp hdom)
  have hC : q ∈ C.source := Classical.choose_spec (mem_iUnion.mp hdom)
  exact C.value_eq_on_overlap B n m hmn ⟨hC,hq⟩

end HillPhysicalAbelianSourceBall

theorem analyticOnNhd_hillHminusPhysicalOffIndexAbelianValue (n m : ℕ+) (hmn : m ≠ n) :
    AnalyticOnNhd ℂ (hillHminusPhysicalOffIndexAbelianValue n m) hillHminusPhysicalAbelianDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  apply (B.analytic_value n m hmn q hB).congr
  filter_upwards [B.source_open.mem_nhds hB] with a ha
  exact (B.canonical_value_eq n m hmn a ha).symm

theorem hillHminusPhysicalAbelianDomain_subset_Dirichlet :
    hillHminusPhysicalAbelianDomain ⊆ hillHminusCanonicalDirichletDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.patch.source_subset_canonicalDirichlet (B.subset hB).1

theorem hillHminusPhysicalAbelianDomain_subset_Psi :
    hillHminusPhysicalAbelianDomain ⊆ hillHminusCanonicalPsiDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact mem_iUnion.mpr ⟨B.patch.parent,B.patch.subset (B.subset hB).1⟩

theorem hillHminusPhysicalOffIndexAbelianValue_eq_patch_of_real (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    hillHminusPhysicalOffIndexAbelianValue n m q = P.physicalOffIndexAbelianValue n m q := by
  obtain ⟨B,hP,_,hB⟩ := exists_hillPhysicalAbelianSourceBall_of_patch P q hq hr
  rw [B.canonical_value_eq n m hmn q hB]
  change B.patch.physicalOffIndexAbelianValue n m q = _
  rw [hP]

theorem hillHminusPhysicalOffIndexAbelianValue_zero_of_sheet_zero (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusPhysicalAbelianDomain)
    (hs : hillHminusDirichletSheet m q = 0) : hillHminusPhysicalOffIndexAbelianValue n m q = 0 := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  rw [B.canonical_value_eq n m hmn q hB]
  exact B.patch.physicalOffIndexAbelianValue_zero_of_sheet_zero n m q hs

theorem exists_common_canonical_physical_Abelian_patch_ball (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ P.physicalDirichletSource ∩ hillHminusPhysicalAbelianDomain ∧
      ∀ n m : ℕ+, m ≠ n → ∀ a ∈ ball q r,
        hillHminusPhysicalOffIndexAbelianValue n m a = P.physicalOffIndexAbelianValue n m a := by
  obtain ⟨B,hP,hcenter,hB⟩ := exists_hillPhysicalAbelianSourceBall_of_patch P q hq hr
  have hsource : B.source = ball q B.radius := by rw [HillPhysicalAbelianSourceBall.source,hcenter]
  refine ⟨B.radius,B.radius_pos,?_,?_⟩
  · intro a ha
    have haB : a ∈ B.source := hsource.symm ▸ ha
    exact ⟨hP ▸ B.subset haB,mem_iUnion.mpr ⟨B,haB⟩⟩
  · intro n m hmn a ha
    have he := B.canonical_value_eq n m hmn a (hsource.symm ▸ ha)
    change hillHminusPhysicalOffIndexAbelianValue n m a = B.patch.physicalOffIndexAbelianValue n m a at he
    simpa only [hP] using he

theorem isConnected_hillHminusPhysicalAbelianDomain : IsConnected hillHminusPhysicalAbelianDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillPhysicalAbelianSourceBall) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real (mem_ball_self B.radius_pos) (convex_ball B.center B.radius).isPreconnected
  have hcommon : (⋂ B : HillPhysicalAbelianSourceBall, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillPhysicalAbelianSourceBall, S ∪ B.source) = hillHminusPhysicalAbelianDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusPhysicalAbelianDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusPhysicalAbelianDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

end NLS.KdV
