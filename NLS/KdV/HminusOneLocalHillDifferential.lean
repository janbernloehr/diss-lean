import NLS.KdV.HminusOneLocalHillPsi
import NLS.KdV.MiuraHillPsiEnergyCycles

/-! Actual local holomorphic energy differentials on original native
H-minus-one source charts. The denominator squares to the physical Hill
radicand and agrees with its normalized physical sheet off the real axis.
Numerator independence between charts is a separate obligation. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillHminusDirichletBall

def energyCoordinates (B : HillHminusDirichletBall) (t : ℂ × PeriodOneHminusOne) : ℂ × Coeff 2 :=
  (t.1,B.miuraBall.actionBall.lift t.2)

def energyDomain (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) : Set (ℂ × PeriodOneHminusOne) :=
  (univ ×ˢ B.psiSource A) ∩ B.energyCoordinates ⁻¹' A.energyRootDomain (B.miuraBall.actionBall.shift:ℂ)

def energyRoot (B : HillHminusDirichletBall) : ℂ × PeriodOneHminusOne → ℂ :=
  (fun s : ℂ × Coeff 2 => hillHminusMiuraRoot s.2 (B.miuraBall.actionBall.shift:ℂ) s.1) ∘ B.energyCoordinates

def energyDifferential (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ := B.psiNumerator A n t/B.energyRoot t

theorem analytic_energyCoordinates (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) :
    AnalyticOnNhd ℂ B.energyCoordinates (univ ×ˢ B.psiSource A) := by
  intro t ht
  exact analyticAt_fst.prod
    ((B.miuraBall.actionBall.lift_analytic t.2 ht.2.1).comp (f := Prod.snd) analyticAt_snd)

theorem energyDomain_open (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) :
    IsOpen (B.energyDomain A) :=
  (B.analytic_energyCoordinates A).continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod (B.psiSource_open A)) (A.energyRootDomain_open _)

theorem mapsTo_energyCoordinates (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) :
    MapsTo B.energyCoordinates (B.energyDomain A)
      (A.energyRootDomain (B.miuraBall.actionBall.shift:ℂ)) :=
  (Set.mapsTo_preimage B.energyCoordinates
    (A.energyRootDomain (B.miuraBall.actionBall.shift:ℂ))).mono_left inter_subset_right

theorem analytic_energyRoot (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) :
    AnalyticOnNhd ℂ B.energyRoot (B.energyDomain A) := by
  unfold HillHminusDirichletBall.energyRoot
  exact (A.analytic_energyRoot (B.miuraBall.actionBall.shift:ℂ)).comp
    ((B.analytic_energyCoordinates A).mono inter_subset_left) (B.mapsTo_energyCoordinates A)

theorem energyRoot_ne_zero (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (t : ℂ × PeriodOneHminusOne) (ht : t ∈ B.energyDomain A) : B.energyRoot t ≠ 0 := by
  simpa only [HillHminusDirichletBall.energyRoot,HillHminusDirichletBall.energyCoordinates,Function.comp_apply] using
    A.energyRoot_ne_zero (B.miuraBall.actionBall.shift:ℂ) (B.energyCoordinates t) (B.mapsTo_energyCoordinates A ht)

theorem energyRoot_sq (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (t : ℂ × PeriodOneHminusOne) (ht : t ∈ B.energyDomain A) :
    B.energyRoot t^2 = hillHminusRadicand t.2 t.1 := by
  have hm := B.mapsTo_energyCoordinates A ht
  rw [HillHminusDirichletBall.energyCoordinates] at hm
  have hs := A.energyRoot_sq t.2 (B.miuraBall.actionBall.shift:ℂ)
    (t.1,B.miuraBall.actionBall.lift t.2) hm (B.miuraBall.actionBall.image t.2 ht.1.2.1)
  simpa only [HillHminusDirichletBall.energyRoot,HillHminusDirichletBall.energyCoordinates,Function.comp_apply] using hs

theorem analytic_energyDifferential (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.energyDifferential A n) (B.energyDomain A) := by
  intro t ht
  exact (B.analytic_psiNumerator A n t ht.1).div
    (B.analytic_energyRoot A t ht) (B.energyRoot_ne_zero A t ht)

theorem energyRoot_eq_physical_of_real (B : HillHminusDirichletBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q)
    (E : ℂ) (hE : E.im ≠ 0) : B.energyRoot (E,q) = hillHminusContinuedRoot (E,q) :=
  hillHminusMiuraRoot_eq_physical_of_real
    ⟨B.miuraBall.actionBall.lift q,B.miuraBall.actionBall.lift_real q hq hr⟩ q
    B.miuraBall.actionBall.shift (B.miuraBall.actionBall.image q hq) E hE

/-- Root equality includes real band values on every available overlap. -/
theorem energyRoot_eq_of_real_overlap (B C : HillHminusDirichletBall) (A D : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (E : ℂ)
    (hB : (E,q) ∈ B.energyDomain A) (hC : (E,q) ∈ C.energyDomain D) :
    B.energyRoot (E,q) = C.energyRoot (E,q) := by
  let u : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift q,
    B.miuraBall.actionBall.lift_real q hB.1.2.1 hr⟩
  let v : PeriodOneRealL2 := ⟨C.miuraBall.actionBall.lift q,
    C.miuraBall.actionBall.lift_real q hC.1.2.1 hr⟩
  exact hillHminusMiuraRoot_eq_of_real_images A D q u v
    B.miuraBall.actionBall.shift C.miuraBall.actionBall.shift
    (B.miuraBall.actionBall.image q hB.1.2.1) (C.miuraBall.actionBall.image q hC.1.2.1)
    ⟨hB.2,hC.2⟩

theorem energyCircle_inside (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ))
    (hpos : 0 < D.center-D.radius) :
    (quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
      (B.miuraBall.actionBall.shift:ℂ)).Inside {E | (E,q) ∈ B.energyDomain A} := by
  have hi := A.energyCircle_inside _ hq.2 (B.miuraBall.actionBall.shift:ℂ) m D hpos
  intro i t
  exact ⟨⟨mem_univ _,hq⟩,hi i t⟩

theorem energyDifferential_circle_period (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A) (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ))
    (hpos : 0 < D.center-D.radius) :
    (2*Real.pi:ℂ)⁻¹*(quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
      (B.miuraBall.actionBall.shift:ℂ)).integral
        (fun E => B.energyDifferential A n (E,q)) = if m = n then 1 else 0 :=
  A.differential_energyCircle_period n m _ hq.2 _ D hpos

end HillHminusDirichletBall
end NLS.KdV
