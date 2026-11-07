import NLS.KdV.HminusOneLocalHillDifferential
import NLS.KdV.MiuraHillPsiFixedShift

/-! Same-shift agreement of local Hill numerators and real-source
differentials. Real-form analytic uniqueness extends numerator agreement
to one common complex neighborhood, selected before all indices and energies. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillHminusDirichletBall

theorem psiNumerator_eq_of_real_same_shift (B C : HillHminusDirichletBall) (A D : MiuraHillPsiFamily)
    (hc : B.miuraBall.actionBall.shift = C.miuraBall.actionBall.shift)
    (q : PeriodOneHminusOne) (hB : q ∈ B.source) (hC : q ∈ C.source)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (E : ℂ) :
    B.psiNumerator A n (E,q) = C.psiNumerator D n (E,q) := by
  let u : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift q,B.miuraBall.actionBall.lift_real q hB hr⟩
  let v : PeriodOneRealL2 := ⟨C.miuraBall.actionBall.lift q,C.miuraBall.actionBall.lift_real q hC hr⟩
  have hu := B.miuraBall.actionBall.image q hB
  rw [hc] at hu
  simpa only [psiNumerator,hc] using A.numerator_eq_of_real_same_shift D q u v
    (C.miuraBall.actionBall.shift:ℂ) hu (C.miuraBall.actionBall.image q hC)
    n (E+(C.miuraBall.actionBall.shift:ℂ))

theorem energyDifferential_eq_of_real_same_shift (B C : HillHminusDirichletBall) (A D : MiuraHillPsiFamily)
    (hc : B.miuraBall.actionBall.shift = C.miuraBall.actionBall.shift)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (E : ℂ)
    (hB : (E,q) ∈ B.energyDomain A) (hC : (E,q) ∈ C.energyDomain D) :
    B.energyDifferential A n (E,q) = C.energyDifferential D n (E,q) := by
  rw [energyDifferential,energyDifferential,
    B.psiNumerator_eq_of_real_same_shift C A D hc q hB.1.2.1 hC.1.2.1 hr n E,
    B.energyRoot_eq_of_real_overlap C A D q hr E hB hC]

theorem exists_complex_same_shift_numerator_agreement
    (B C : HillHminusDirichletBall) (A D : MiuraHillPsiFamily)
    (hc : B.miuraBall.actionBall.shift = C.miuraBall.actionBall.shift)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hB : q ∈ B.psiSource A) (hC : q ∈ C.psiSource D) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ B.psiSource A ∩ C.psiSource D ∧
      ∀ n : ℕ+, ∀ E : ℂ, EqOn (fun a => B.psiNumerator A n (E,a))
        (fun a => C.psiNumerator D n (E,a)) U := by
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp
    (((B.psiSource_open A).inter (C.psiSource_open D)).mem_nhds ⟨hB,hC⟩)
  refine ⟨ball q r,isOpen_ball,mem_ball_self hrpos,hball,?_⟩
  intro n E
  apply analytic_eqOn_of_real_periodOneHminus (ball q r) isOpen_ball
    (convex_ball q r).isPreconnected ⟨q,mem_ball_self hrpos,hr⟩ _ _
  · intro a ha
    exact (B.analytic_psiNumerator A n (E,a) ⟨mem_univ _,(hball ha).1⟩).comp
      (f := fun b : PeriodOneHminusOne => (E,b)) (analyticAt_const.prod analyticAt_id)
  · intro a ha
    exact (C.analytic_psiNumerator D n (E,a) ⟨mem_univ _,(hball ha).2⟩).comp
      (f := fun b : PeriodOneHminusOne => (E,b)) (analyticAt_const.prod analyticAt_id)
  · intro a ha har
    exact B.psiNumerator_eq_of_real_same_shift C A D hc a (hball ha).1.1 (hball ha).2.1 har n E

end HillHminusDirichletBall
end NLS.KdV
