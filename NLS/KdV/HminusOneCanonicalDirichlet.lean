import NLS.KdV.HminusOneDirichletAnalyticBalls

/-! # Canonical analytic simple Dirichlet coordinates on one common domain

Real-centered Miura balls agree on entire complex overlaps because they
give the SAME original real Dirichlet labels. ALL resulting coordinates
are analytic and simple on ONE connected complex neighborhood of the
entire real form, alongside the canonical actions and squared gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped Classical
namespace NLS.KdV

def hillHminusCanonicalDirichletDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillHminusDirichletBall, B.source

theorem isOpen_hillHminusCanonicalDirichletDomain : IsOpen hillHminusCanonicalDirichletDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem hillHminusCanonicalDirichletDomain_subset :
    hillHminusCanonicalDirichletDomain ⊆ hillHminusCanonicalRatioDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.subset_ratio hB

theorem real_mem_hillHminusCanonicalDirichletDomain (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : q ∈ hillHminusCanonicalDirichletDomain := by
  obtain ⟨B,hB⟩ := exists_hillHminusDirichletBall q hq
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem isConnected_hillHminusCanonicalDirichletDomain : IsConnected hillHminusCanonicalDirichletDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillHminusDirichletBall) : IsPreconnected (S ∪ B.source) :=
    hS.union B.miuraBall.actionBall.center B.miuraBall.actionBall.center_real
      (mem_ball_self B.miuraBall.actionBall.radius_pos)
      (convex_ball B.miuraBall.actionBall.center B.miuraBall.actionBall.radius).isPreconnected
  have hcommon : (⋂ B : HillHminusDirichletBall, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillHminusDirichletBall, S ∪ B.source) = hillHminusCanonicalDirichletDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusCanonicalDirichletDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusCanonicalDirichletDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

def hillHminusCanonicalDirichlet (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  if hq : q ∈ hillHminusCanonicalDirichletDomain then
    (Classical.choose (mem_iUnion.mp hq)).energy n q
  else 0

theorem HillHminusDirichletBall.canonical_dirichlet_eq (B : HillHminusDirichletBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) : hillHminusCanonicalDirichlet n q = B.energy n q := by
  have hdom : q ∈ hillHminusCanonicalDirichletDomain := mem_iUnion.mpr ⟨B,hq⟩
  rw [hillHminusCanonicalDirichlet,dif_pos hdom]
  let C : HillHminusDirichletBall := Classical.choose (mem_iUnion.mp hdom)
  have hC : q ∈ C.source := Classical.choose_spec (mem_iUnion.mp hdom)
  exact C.energy_eq_on_overlap B n ⟨hC,hq⟩

theorem analyticOnNhd_hillHminusCanonicalDirichlet (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalDirichlet n) hillHminusCanonicalDirichletDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  apply (B.analytic_energy n q hB).congr
  filter_upwards [B.source_open.mem_nhds hB] with a ha
  exact (B.canonical_dirichlet_eq n a ha).symm

theorem hillHminusCanonicalDirichlet_eq_real (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusCanonicalDirichlet n q = (hillHminusDirichletLabels q hq n : ℂ) := by
  obtain ⟨B,hB⟩ := exists_hillHminusDirichletBall q hq
  exact (B.canonical_dirichlet_eq n q hB).trans (B.energy_eq_real n q hB hq)

theorem hillHminusCanonicalDirichlet_is_root (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    hillHminusDirichlet q (hillHminusCanonicalDirichlet n q) = 0 := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  rw [B.canonical_dirichlet_eq n q hB]
  exact B.energy_is_root n q hB

theorem deriv_hillHminusCanonicalDirichlet_ne_zero (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet n q) ≠ 0 := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  rw [B.canonical_dirichlet_eq n q hB]
  exact B.simple n q hB

theorem hillHminusCanonicalDirichlet_native_multiplicity (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    singularDirichletAlgebraicMultiplicity (periodOneOriginal q) (hillHminusCanonicalDirichlet n q) = 1 := by
  have ho := (analyticOnNhd_hillHminusDirichlet_energy q _ (mem_univ _)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (hillHminusCanonicalDirichlet_is_root n q hq) (deriv_hillHminusCanonicalDirichlet_ne_zero n q hq)
  rw [singularDirichletAlgebraicMultiplicity_eq_analyticOrderNatAt,analyticOrderNatAt,ho]
  rfl

theorem exists_hillHminusCanonicalDirichlet_uniform_high_comparison
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, 0 < N ∧ IsOpen U ∧ q ∈ U ∧
      U ⊆ hillHminusCanonicalDirichletDomain ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → EqOn (hillHminusCanonicalDirichlet n)
        (fun a => hillHminusDirichletComplexLabels a n) U := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  refine ⟨B.cutoff+1,B.source,by omega,B.source_open,hB,(fun a ha => mem_iUnion.mpr ⟨B,ha⟩),?_⟩
  intro n hn a ha
  exact (B.canonical_dirichlet_eq n a ha).trans (B.energy_eq_high n (by omega) a ha)

end NLS.KdV
