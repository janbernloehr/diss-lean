import NLS.KdV.HminusOneHillPsiBalls

/-! Intrinsic normalized Hill energy numerators on ONE open connected
complex neighborhood of the ENTIRE native real H-minus-one form. ALL
indices use the same domain, contained in the existing common divisor,
action and squared-gap domains. Joint analyticity includes every energy.
The whole-overlap theorem makes the choice independent of actual psi
families, Miura lifts and physical shifts. Values outside the domain
are only a total-function convention. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusCanonicalPsiDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillHminusPsiBall, B.source

theorem isOpen_hillHminusCanonicalPsiDomain : IsOpen hillHminusCanonicalPsiDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem hillHminusCanonicalPsiDomain_subset_dirichletDomain :
    hillHminusCanonicalPsiDomain ⊆ hillHminusCanonicalDirichletDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.source_subset_dirichletDomain hB

theorem real_mem_hillHminusCanonicalPsiDomain (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : q ∈ hillHminusCanonicalPsiDomain := by
  obtain ⟨A⟩ := nonempty_miuraHillPsiFamily
  obtain ⟨B,_,_,hB⟩ := exists_hillHminusPsiBall A q hq
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem isConnected_hillHminusCanonicalPsiDomain : IsConnected hillHminusCanonicalPsiDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillHminusPsiBall) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real (mem_ball_self B.radius_pos) (convex_ball B.center B.radius).isPreconnected
  have hcommon : (⋂ B : HillHminusPsiBall, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillHminusPsiBall, S ∪ B.source) = hillHminusCanonicalPsiDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusCanonicalPsiDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusCanonicalPsiDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

/-- A source chart is chosen once for a source, before all indices and energies. -/
def hillHminusCanonicalPsi (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  if hq : t.2 ∈ hillHminusCanonicalPsiDomain then
    (Classical.choose (mem_iUnion.mp hq)).numerator n t
  else 0

theorem HillHminusPsiBall.canonical_numerator_eq (B : HillHminusPsiBall) (n : ℕ+) (E : ℂ)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    hillHminusCanonicalPsi n (E,q) = B.numerator n (E,q) := by
  have hdom : q ∈ hillHminusCanonicalPsiDomain := mem_iUnion.mpr ⟨B,hq⟩
  rw [hillHminusCanonicalPsi,dif_pos hdom]
  let C : HillHminusPsiBall := Classical.choose (mem_iUnion.mp hdom)
  have hC : q ∈ C.source := Classical.choose_spec (mem_iUnion.mp hdom)
  exact C.numerator_eq_on_overlap B n E ⟨hC,hq⟩

theorem analyticOnNhd_hillHminusCanonicalPsi (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalPsi n) (univ ×ˢ hillHminusCanonicalPsiDomain) := by
  intro t ht
  obtain ⟨B,hB⟩ := mem_iUnion.mp ht.2
  apply (B.analytic_numerator n t ⟨mem_univ _,hB⟩).congr
  filter_upwards [(isOpen_univ.prod B.source_open).mem_nhds ⟨mem_univ t.1,hB⟩] with a ha
  exact (B.canonical_numerator_eq n a.1 a.2 ha.2).symm

theorem hillHminusCanonicalPsi_energy_entire (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalPsiDomain) :
    AnalyticOnNhd ℂ (fun E : ℂ => hillHminusCanonicalPsi n (E,q)) univ := by
  intro E _
  exact (analyticOnNhd_hillHminusCanonicalPsi n (E,q) ⟨mem_univ _,hq⟩).comp
    (f := fun e : ℂ => (e,q)) (analyticAt_id.prod analyticAt_const)

theorem hillHminusCanonicalPsi_eq_local_of_real (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hq : q ∈ B.psiSource A)
    (n : ℕ+) (E : ℂ) : hillHminusCanonicalPsi n (E,q) = B.psiNumerator A n (E,q) := by
  obtain ⟨C,hB,hA,_,hC⟩ := exists_hillHminusPsiBall_of_mem B A q hr hq
  rw [C.canonical_numerator_eq n E q hC]
  simp only [HillHminusPsiBall.numerator,hB,hA]

/-- One local presentation serves ALL energies and ALL positive indices. -/
theorem exists_hillHminusCanonicalPsi_local_presentation (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalPsiDomain) :
    ∃ B : HillHminusPsiBall, q ∈ B.source ∧ B.source ⊆ hillHminusCanonicalPsiDomain ∧
      ∀ n : ℕ+, ∀ E : ℂ, EqOn (fun a => hillHminusCanonicalPsi n (E,a))
        (fun a => B.numerator n (E,a)) B.source := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact ⟨B,hB,(fun a ha => mem_iUnion.mpr ⟨B,ha⟩),fun n E a ha => B.canonical_numerator_eq n E a ha⟩

end NLS.KdV
