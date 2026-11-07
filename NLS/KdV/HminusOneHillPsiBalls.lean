import NLS.KdV.HminusOneHillPsiIndependence

/-! Real-centered balls inside actual simultaneous Hill numerator
patches. Convex intersections meet the native real form, so agreement
extends to WHOLE complex overlaps at every index and energy. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

structure HillHminusPsiBall where
  parent : HillHminusDirichletBall
  family : MiuraHillPsiFamily
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  subset : ball center radius ⊆ parent.psiSource family

namespace HillHminusPsiBall

def source (B : HillHminusPsiBall) : Set PeriodOneHminusOne := ball B.center B.radius

def numerator (B : HillHminusPsiBall) (n : ℕ+) : ℂ × PeriodOneHminusOne → ℂ :=
  B.parent.psiNumerator B.family n

theorem source_open (B : HillHminusPsiBall) : IsOpen B.source := isOpen_ball

theorem source_subset_dirichletDomain (B : HillHminusPsiBall) :
    B.source ⊆ hillHminusCanonicalDirichletDomain :=
  fun _ hq => B.parent.psiSource_subset_dirichletDomain B.family (B.subset hq)

theorem analytic_numerator (B : HillHminusPsiBall) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.numerator n) (univ ×ˢ B.source) :=
  (B.parent.analytic_psiNumerator B.family n).mono (prod_mono Subset.rfl B.subset)

theorem numerator_eq_on_overlap (B C : HillHminusPsiBall) (n : ℕ+) (E : ℂ) :
    EqOn (fun q => B.numerator n (E,q)) (fun q => C.numerator n (E,q)) (B.source ∩ C.source) := by
  intro q hq
  have hreal : ∃ a ∈ B.source ∩ C.source, IsRealPeriodOneHminusOne a :=
    exists_real_mem_periodOneHminus_ball_inter B.center C.center B.center_real C.center_real
      B.radius C.radius ⟨q,hq⟩
  apply analytic_eqOn_of_real_periodOneHminus (B.source ∩ C.source) (B.source_open.inter C.source_open)
    ((convex_ball B.center B.radius).inter (convex_ball C.center C.radius)).isPreconnected hreal
    _ _ _ _ _ hq
  · intro a ha
    exact (B.analytic_numerator n (E,a) ⟨mem_univ _,ha.1⟩).comp
      (f := fun b : PeriodOneHminusOne => (E,b)) (analyticAt_const.prod analyticAt_id)
  · intro a ha
    exact (C.analytic_numerator n (E,a) ⟨mem_univ _,ha.2⟩).comp
      (f := fun b : PeriodOneHminusOne => (E,b)) (analyticAt_const.prod analyticAt_id)
  · intro a ha har
    exact B.parent.psiNumerator_eq_of_real_overlap C.parent B.family C.family a
      (B.subset ha.1).1 (C.subset ha.2).1 har n E

end HillHminusPsiBall

theorem exists_hillHminusPsiBall_of_mem (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hq : q ∈ B.psiSource A) :
    ∃ C : HillHminusPsiBall, C.parent = B ∧ C.family = A ∧ C.center = q ∧ q ∈ C.source := by
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp ((B.psiSource_open A).mem_nhds hq)
  exact ⟨⟨B,A,q,hr,r,hrpos,hball⟩,rfl,rfl,rfl,mem_ball_self hrpos⟩

theorem exists_hillHminusPsiBall (A : MiuraHillPsiFamily) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ B : HillHminusPsiBall, B.family = A ∧ B.center = q ∧ q ∈ B.source := by
  obtain ⟨C,hC⟩ := exists_local_hminusHillPsiFamily A q hr
  obtain ⟨B,_,hA,hq,hB⟩ := exists_hillHminusPsiBall_of_mem C A q hr hC
  exact ⟨B,hA,hq,hB⟩

end NLS.KdV
