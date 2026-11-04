import NLS.KdV.HillHminusOneMiuraGapBalls

/-! The ACTUAL original positive Hill gap midpoint on every common
native Miura ball. The formula uses the analytic Dirac midpoint and
squared gap, so all low and collapsed gaps are included. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillHminusMiuraGapBall

def energyMidpoint (B : HillHminusMiuraGapBall) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  (sourceStandardRootMidpoint (by norm_num) (by norm_num)
    (hillMiuraDiagonal (B.actionBall.lift q)) (n:ℕ))^2+
    (canonicalPeriodicGap (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal (B.actionBall.lift q))) (periodOnePotential_mem _) (n:ℕ))^2/4-
      (B.actionBall.shift:ℂ)

theorem analytic_energyMidpoint (B : HillHminusMiuraGapBall) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.energyMidpoint n) B.source := by
  intro q hq
  exact (((B.midpoint_analytic (n:ℕ) q hq).pow 2).add
    ((B.dirac_gap_square_analytic (n:ℕ) q hq).div_const)).sub analyticAt_const

theorem energyMidpoint_eq_real (B : HillHminusMiuraGapBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) :
    B.energyMidpoint n q =
      ((hillHminusLabels q hr (2*(n:ℕ)-1):ℂ)+(hillHminusLabels q hr (2*(n:ℕ)):ℂ))/2 := by
  let u : PeriodOneRealL2 := ⟨B.actionBall.lift q,B.actionBall.lift_real q hq hr⟩
  have he := hillHminusLabels_pair_eq_squared_miuraDirac q hr u B.actionBall.shift
    (B.actionBall.image q hq) (B.actionBall.outside q hq) (n:ℕ) n.pos
  have hre := hillMiuraDiracPair_real u (n:ℕ)
  have hl : ((hillMiuraDiracLeft u.val (n:ℕ)).re:ℂ) = hillMiuraDiracLeft u.val (n:ℕ) :=
    Complex.ext rfl hre.1.symm
  have hu : ((hillMiuraDiracRight u.val (n:ℕ)).re:ℂ) = hillMiuraDiracRight u.val (n:ℕ) :=
    Complex.ext rfl hre.2.symm
  rw [he.1,he.2,Complex.ofReal_sub,Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_pow,hl,hu]
  change ((hillMiuraDiracLeft u.val (n:ℕ)+hillMiuraDiracRight u.val (n:ℕ))/2)^2+
    (hillMiuraDiracRight u.val (n:ℕ)-hillMiuraDiracLeft u.val (n:ℕ))^2/4-(B.actionBall.shift:ℂ) = _
  ring

theorem energyMidpoint_eq_on_overlap (B C : HillHminusMiuraGapBall) (n : ℕ+) :
    EqOn (B.energyMidpoint n) (C.energyMidpoint n) (B.source ∩ C.source) := by
  intro q hq
  have hreal : ∃ a ∈ B.source ∩ C.source, IsRealPeriodOneHminusOne a :=
    exists_real_mem_periodOneHminus_ball_inter B.actionBall.center C.actionBall.center
      B.actionBall.center_real C.actionBall.center_real B.actionBall.radius C.actionBall.radius ⟨q,hq⟩
  exact analytic_eqOn_of_real_periodOneHminus (B.source ∩ C.source)
    (B.source_open.inter C.source_open) ((convex_ball B.actionBall.center B.actionBall.radius).inter
      (convex_ball C.actionBall.center C.actionBall.radius)).isPreconnected hreal
    (B.energyMidpoint n) (C.energyMidpoint n)
    ((B.analytic_energyMidpoint n).mono inter_subset_left) ((C.analytic_energyMidpoint n).mono inter_subset_right)
    (fun a ha har => (B.energyMidpoint_eq_real n a ha.1 har).trans
      (C.energyMidpoint_eq_real n a ha.2 har).symm) hq

end HillHminusMiuraGapBall
end NLS.KdV
