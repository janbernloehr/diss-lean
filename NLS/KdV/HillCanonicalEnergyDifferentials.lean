import NLS.KdV.HillCanonicalEnergyRoot
import NLS.ComplexAnalysis.PiecewiseContourCongruence

/-! ALL normalized intrinsic Hill energy differentials on the SAME
OPEN JOINT energy/native-source sheet domain. Whole complex box
agreements retain the exact local physical differential and, at every
real source, the original one-over-two-pi positive cycle periods. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusCanonicalEnergyDifferential (n : ℕ+) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillHminusCanonicalPsi n t/hillHminusCanonicalEnergyRoot t

theorem analyticOnNhd_hillHminusCanonicalEnergyDifferential (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalEnergyDifferential n) hillHminusCanonicalEnergyRootDomain := by
  intro t ht
  have hsource := (hillHminusCanonicalEnergyRootDomain_subset_simpleSource ht).2
  have hpsi := hillHminusCanonicalZeroSequenceDomain_subset_psiDomain
    (hillHminusSimpleZeroSequenceDomain_subset_zeroDomain hsource)
  exact (analyticOnNhd_hillHminusCanonicalPsi n t ⟨mem_univ _,hpsi⟩).div
    (analyticOnNhd_hillHminusCanonicalEnergyRoot t ht) (hillHminusCanonicalEnergyRoot_ne_zero t ht)

theorem HillHminusEnergyRootBox.canonical_numerator_eq (B : HillHminusEnergyRootBox)
    (n : ℕ+) (E : ℂ) (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    hillHminusCanonicalPsi n (E,q) = B.parent.psiNumerator B.family n (E,q) := by
  have hsub : ball B.center B.radius ⊆ B.parent.psiSource B.family := by
    intro a ha
    have ht : (B.energyCenter,a) ∈ B.domain := ⟨mem_ball_self B.energyRadius_pos,ha⟩
    exact (B.subset ht).1.2
  let C : HillHminusPsiBall := ⟨B.parent,B.family,B.center,B.center_real,B.radius,B.radius_pos,hsub⟩
  exact C.canonical_numerator_eq n E q hq

theorem HillHminusEnergyRootBox.canonical_differential_eq (B : HillHminusEnergyRootBox)
    (n : ℕ+) (t : ℂ × PeriodOneHminusOne) (ht : t ∈ B.domain) :
    hillHminusCanonicalEnergyDifferential n t = B.parent.energyDifferential B.family n t := by
  rcases t with ⟨E,q⟩
  rw [hillHminusCanonicalEnergyDifferential,B.canonical_root_eq (E,q) ht,B.canonical_numerator_eq n E q ht.2]
  rfl

theorem hillHminusCanonicalEnergyDifferential_eq_local_of_real
    (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) (n : ℕ+) (E : ℂ) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (ht : (E,q) ∈ B.energyDomain A) :
    hillHminusCanonicalEnergyDifferential n (E,q) = B.energyDifferential A n (E,q) := by
  obtain ⟨C,hparent,hfamily,_,_,hC⟩ := exists_hillHminusEnergyRootBox_of_real_mem B A E q hr ht
  rw [C.canonical_differential_eq n (E,q) hC]
  rw [hparent,hfamily]

theorem hillHminusCanonicalEnergyDifferential_eq_physical_of_real
    (n : ℕ+) (E : ℂ) (hE : E.im ≠ 0) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    hillHminusCanonicalEnergyDifferential n (E,q) = hillHminusCanonicalPsi n (E,q)/hillHminusContinuedRoot (E,q) := by
  rw [hillHminusCanonicalEnergyDifferential,hillHminusCanonicalEnergyRoot_eq_physical_of_real E hE q hr]

theorem HillHminusDirichletBall.canonical_energyCircle_inside (B : HillHminusDirichletBall)
    (A : MiuraHillPsiFamily) (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A)
    (hr : IsRealPeriodOneHminusOne q) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ))
    (hpos : 0 < D.center-D.radius) :
    (quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
      (B.miuraBall.actionBall.shift:ℂ)).Inside {E | (E,q) ∈ hillHminusCanonicalEnergyRootDomain} := by
  intro i t
  exact real_mem_hillHminusCanonicalEnergyRootDomain_of_local B A _ q hr (B.energyCircle_inside A q hq m D hpos i t)

theorem HillHminusDirichletBall.canonical_energyDifferential_circle_period (B : HillHminusDirichletBall)
    (A : MiuraHillPsiFamily) (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A)
    (hr : IsRealPeriodOneHminusOne q) (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ))
    (hpos : 0 < D.center-D.radius) :
    (2*Real.pi:ℂ)⁻¹*(quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
      (B.miuraBall.actionBall.shift:ℂ)).integral
        (fun E => hillHminusCanonicalEnergyDifferential n (E,q)) = if m = n then 1 else 0 := by
  let Γ := quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius) (B.miuraBall.actionBall.shift:ℂ)
  have hi := B.energyCircle_inside A q hq m D hpos
  have he : Γ.integral (fun E => hillHminusCanonicalEnergyDifferential n (E,q)) =
      Γ.integral (fun E => B.energyDifferential A n (E,q)) := Γ.integral_congr hi
    (fun E hE => hillHminusCanonicalEnergyDifferential_eq_local_of_real B A n E q hr hE)
  rw [he]
  exact B.energyDifferential_circle_period A q hq n m D hpos

end NLS.KdV
