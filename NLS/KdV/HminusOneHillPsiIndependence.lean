import NLS.KdV.HillMiuraComparisonPeriods
import NLS.KdV.HillPsiPeriodUniqueness

/-! Actual native Hill numerators agree at EVERY real overlap, for
arbitrary verified Miura lifts, shifts and simultaneous psi families.
Actual common periods are proved, rather than imposed as a hypothesis.
Real-form uniqueness gives one complex neighborhood before all indices
and all energies. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillHminusDirichletBall

theorem psiNumerator_eq_of_real_overlap (B C : HillHminusDirichletBall) (A D : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hB : q ∈ B.source) (hC : q ∈ C.source)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (E : ℂ) :
    B.psiNumerator A n (E,q) = C.psiNumerator D n (E,q) := by
  let u : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift q,B.miuraBall.actionBall.lift_real q hB hr⟩
  let v : PeriodOneRealL2 := ⟨C.miuraBall.actionBall.lift q,C.miuraBall.actionBall.lift_real q hC hr⟩
  let c := B.miuraBall.actionBall.shift
  let d := C.miuraBall.actionBall.shift
  have hu : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)) :=
    B.miuraBall.actionBall.image q hB
  have hv : periodOneMiura v.val = q+periodOneL2Inclusion (lp.single 2 0 (d:ℂ)) :=
    C.miuraBall.actionBall.image q hC
  have hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q) := B.miuraBall.actionBall.outside q hB
  have hd : -(d:ℂ) ∉ singularHillSpectrum (periodOneOriginal q) := C.miuraBall.actionBall.outside q hC
  have he := B.psiNumerator_eq_of_positive_common_periods C A D q u n (c:ℂ) (by
    intro m
    obtain ⟨S,T,hS,hT,Γ,hΓ,hw⟩ := exists_common_hillMiura_gap_contour q hr u v c d hu hv hc hd m
    refine ⟨S,?_⟩
    have hΓS : Γ.Inside (energyFrequencyDisk (c:ℂ) (S.center:ℂ) S.radius \
        Complex.ofReal '' Icc (hillHminusLabels q hr (2*(m:ℕ)-1)) (hillHminusLabels q hr (2*(m:ℕ)))) :=
      fun i t => ⟨(hΓ i t).1.1,(hΓ i t).2⟩
    have hF : AnalyticOnNhd ℂ (fun z : ℂ =>
        2*z*(B.psiNumerator A n (z^2-(c:ℂ),q)-C.psiNumerator D n (z^2-(c:ℂ),q))) univ := by
      have he : (fun z : ℂ => 2*z*(B.psiNumerator A n (z^2-(c:ℂ),q)-C.psiNumerator D n (z^2-(c:ℂ),q))) =
          (fun z : ℂ => 2*z*B.psiNumerator A n (z^2-(c:ℂ),q)-2*z*C.psiNumerator D n (z^2-(c:ℂ),q)) := by
        funext z
        ring
      rw [he]
      exact (B.psiNumerator_arbitrary_shift_pullback_entire A q n (c:ℂ)).sub
        (C.psiNumerator_arbitrary_shift_pullback_entire D q n (c:ℂ))
    apply hillMiura_circle_zero_of_energy_difference_zero q hr u c hu hc m S hS Γ
      (fun i t => (hΓS i t).1.1) hΓS hw
      (fun e => B.psiNumerator A n (e,q)) (fun e => C.psiNumerator D n (e,q)) hF
    exact hillMiura_common_energy_difference_zero A D q hr u v c d hu hv hc hd m S T hS hT Γ hΓ hw n)
  exact congrFun he E

theorem energyDifferential_eq_of_real_overlap (B C : HillHminusDirichletBall) (A D : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (E : ℂ)
    (hB : (E,q) ∈ B.energyDomain A) (hC : (E,q) ∈ C.energyDomain D) :
    B.energyDifferential A n (E,q) = C.energyDifferential D n (E,q) := by
  rw [energyDifferential,energyDifferential,
    B.psiNumerator_eq_of_real_overlap C A D q hB.1.2.1 hC.1.2.1 hr n E,
    B.energyRoot_eq_of_real_overlap C A D q hr E hB hC]

theorem exists_complex_numerator_agreement
    (B C : HillHminusDirichletBall) (A D : MiuraHillPsiFamily)
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
    exact B.psiNumerator_eq_of_real_overlap C A D a (hball ha).1.1 (hball ha).2.1 har n E

end HillHminusDirichletBall
end NLS.KdV
