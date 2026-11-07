import NLS.KdV.HillCommonSimpleComplexZeroDomain
import NLS.KdV.HminusOneLocalHillDifferential
import NLS.ZakharovShabat.SourceCriticalRootRatioTransverseBound

/-! Joint energy/source boxes for the ACTUAL physical Hill energy
sheet. Source centers are REAL; energy centers may be arbitrary complex
points. This makes every nonempty source overlap meet the real form. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

structure HillHminusEnergyRootBox where
  parent : HillHminusDirichletBall
  family : MiuraHillPsiFamily
  energyCenter : ℂ
  energyRadius : ℝ
  energyRadius_pos : 0 < energyRadius
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  subset : ball energyCenter energyRadius ×ˢ ball center radius ⊆ parent.energyDomain family
  source_subset : ball center radius ⊆ hillHminusSimpleZeroSequenceDomain

namespace HillHminusEnergyRootBox

def source (B : HillHminusEnergyRootBox) : Set PeriodOneHminusOne := ball B.center B.radius

def domain (B : HillHminusEnergyRootBox) : Set (ℂ × PeriodOneHminusOne) := ball B.energyCenter B.energyRadius ×ˢ B.source

def root (B : HillHminusEnergyRootBox) : ℂ × PeriodOneHminusOne → ℂ := B.parent.energyRoot

theorem domain_open (B : HillHminusEnergyRootBox) : IsOpen B.domain := isOpen_ball.prod isOpen_ball

theorem analytic_root (B : HillHminusEnergyRootBox) : AnalyticOnNhd ℂ B.root B.domain :=
  (B.parent.analytic_energyRoot B.family).mono B.subset

theorem root_ne_zero (B : HillHminusEnergyRootBox) (t : ℂ × PeriodOneHminusOne) (ht : t ∈ B.domain) :
    B.root t ≠ 0 := B.parent.energyRoot_ne_zero B.family t (B.subset ht)

theorem root_sq (B : HillHminusEnergyRootBox) (t : ℂ × PeriodOneHminusOne) (ht : t ∈ B.domain) :
    B.root t^2 = hillHminusRadicand t.2 t.1 := B.parent.energyRoot_sq B.family t (B.subset ht)

theorem root_eq_on_overlap (B C : HillHminusEnergyRootBox) : EqOn B.root C.root (B.domain ∩ C.domain) := by
  intro t ht
  have hreal : ∃ a ∈ B.source ∩ C.source, IsRealPeriodOneHminusOne a :=
    exists_real_mem_periodOneHminus_ball_inter B.center C.center B.center_real C.center_real
      B.radius C.radius ⟨t.2,ht.1.2,ht.2.2⟩
  have hB : AnalyticOnNhd ℂ (fun a => B.root (t.1,a)) (B.source ∩ C.source) := by
    intro a ha
    exact (B.analytic_root (t.1,a) ⟨ht.1.1,ha.1⟩).comp
      (f := fun b : PeriodOneHminusOne => (t.1,b)) (analyticAt_const.prod analyticAt_id)
  have hC : AnalyticOnNhd ℂ (fun a => C.root (t.1,a)) (B.source ∩ C.source) := by
    intro a ha
    exact (C.analytic_root (t.1,a) ⟨ht.2.1,ha.2⟩).comp
      (f := fun b : PeriodOneHminusOne => (t.1,b)) (analyticAt_const.prod analyticAt_id)
  exact analytic_eqOn_of_real_periodOneHminus _ (isOpen_ball.inter isOpen_ball)
    ((convex_ball B.center B.radius).inter (convex_ball C.center C.radius)).isPreconnected hreal _ _ hB hC
    (fun a ha har => B.parent.energyRoot_eq_of_real_overlap C.parent B.family C.family a har t.1
      (B.subset ⟨ht.1.1,ha.1⟩) (C.subset ⟨ht.2.1,ha.2⟩)) ⟨ht.1.2,ht.2.2⟩

end HillHminusEnergyRootBox

theorem exists_hillHminusEnergyRootBox_of_real_mem (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (E : ℂ) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (ht : (E,q) ∈ B.energyDomain A) :
    ∃ C : HillHminusEnergyRootBox, C.parent = B ∧ C.family = A ∧ C.energyCenter = E ∧ C.center = q ∧ (E,q) ∈ C.domain := by
  let U := B.energyDomain A ∩ (univ ×ˢ hillHminusSimpleZeroSequenceDomain)
  have hU : IsOpen U := (B.energyDomain_open A).inter (isOpen_univ.prod isOpen_hillHminusSimpleZeroSequenceDomain)
  have hEU : (E,q) ∈ U := ⟨ht,mem_univ _,real_mem_hillHminusSimpleZeroSequenceDomain q hr⟩
  obtain ⟨r,hrpos,hball⟩ := Metric.isOpen_iff.mp hU (E,q) hEU
  have hprod : ball E r ×ˢ ball q r ⊆ U := by
    intro t ht
    apply hball
    rw [mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨ht.1,ht.2⟩
  have hsub : ball E r ×ˢ ball q r ⊆ B.energyDomain A := fun t ht => (hprod ht).1
  have hsource : ball q r ⊆ hillHminusSimpleZeroSequenceDomain := by
    intro a ha
    have hh : (E,a) ∈ U := hprod (show (E,a) ∈ ball E r ×ˢ ball q r from ⟨mem_ball_self hrpos,ha⟩)
    exact hh.2.2
  let C : HillHminusEnergyRootBox := {
    parent := B
    family := A
    energyCenter := E
    energyRadius := r
    energyRadius_pos := hrpos
    center := q
    center_real := hr
    radius := r
    radius_pos := hrpos
    subset := hsub
    source_subset := hsource }
  refine ⟨C,rfl,rfl,rfl,rfl,?_⟩
  exact ⟨mem_ball_self hrpos,mem_ball_self hrpos⟩

theorem HillHminusDirichletBall.nonreal_energy_mem_domain (B : HillHminusDirichletBall)
    (A : MiuraHillPsiFamily) (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A)
    (hr : IsRealPeriodOneHminusOne q) (E : ℂ) (hE : E.im ≠ 0) : (E,q) ∈ B.energyDomain A := by
  let c : ℝ := B.miuraBall.actionBall.shift
  let u : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift q,B.miuraBall.actionBall.lift_real q hq.1 hr⟩
  have hreal := (hillMiuraRealSource u).property
  have him : (E+(c:ℂ)).im ≠ 0 := by simpa only [add_im,ofReal_im,add_zero] using hE
  have hsqrt : (Complex.sqrt (E+(c:ℂ))).im ≠ 0 := by
    intro hz
    have hh := congrArg Complex.im (complex_sqrt_sq (E+(c:ℂ)))
    simp only [pow_two,mul_im,hz,mul_zero,zero_mul,add_zero] at hh
    exact him hh.symm
  refine ⟨⟨mem_univ _,hq⟩,hq.2,mem_slitPlane_iff.mpr (Or.inr him),?_⟩
  intro k hk
  exact hsqrt (sourcePeriodicSegment_im_eq_zero_of_realType (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) hreal k _ hk)

end NLS.KdV
