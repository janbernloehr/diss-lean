import NLS.KdV.HillHminusOneDirichletColumnCharts
import NLS.KdV.HillHminusOneDirichletRealColumn

/-! # One intrinsic entire normalized H^-1 Dirichlet scalar curve

The target is the full continuous interval-curve Banach space with its
uniform norm. Every shifted-Miura chart recovers this same normalized
curve, at every complex potential and energy. It is jointly entire and
its terminal value is the original normalized Dirichlet characteristic.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory hiding extend
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

theorem HillHminusMiuraChart.analyticOnNhd_physicalPosition (C : HillHminusMiuraChart) (v : ℂ × ℂ) :
    AnalyticOnNhd ℂ (fun p : ℂ × PeriodOneHminusOne => C.physicalPosition p.2 p.1 v)
      (univ ×ˢ C.domain) := by
  intro p hp
  exact ((ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1)
    (ContinuousLinearMap.fst ℂ ℂ ℂ)).analyticAt _).comp (C.analyticOnNhd_physicalSolution v p hp)

theorem HillHminusMiuraChart.analyticOnNhd_physicalMomentum (C : HillHminusMiuraChart) (v : ℂ × ℂ) :
    AnalyticOnNhd ℂ (fun p : ℂ × PeriodOneHminusOne => C.physicalMomentum p.2 p.1 v)
      (univ ×ˢ C.domain) := by
  intro p hp
  exact ((ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1)
    (ContinuousLinearMap.snd ℂ ℂ ℂ)).analyticAt _).comp (C.analyticOnNhd_physicalSolution v p hp)

def hillHminusDirichletColumn (q : PeriodOneHminusOne) (lambda : ℂ) : Curve ℂ :=
  (hillHminusMiuraChartAt q).physicalPosition q lambda (0,1)

theorem hillHminusDirichletColumn_eq_chart (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (lambda : ℂ) :
    hillHminusDirichletColumn q lambda = C.physicalPosition q lambda (0,1) :=
  (hillHminusMiuraChartAt q).dirichlet_position_eq_on_overlap C q (mem_hillHminusMiuraChartAt q) hq lambda

theorem analyticOnNhd_hillHminusDirichletColumn_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × PeriodOneHminusOne => hillHminusDirichletColumn p.2 p.1) univ := by
  intro p _
  let C := hillHminusMiuraChartAt p.2
  have hp : p ∈ univ ×ˢ C.domain := ⟨mem_univ _,mem_hillHminusMiuraChartAt _⟩
  apply (C.analyticOnNhd_physicalPosition (0,1) p hp).congr
  filter_upwards [(isOpen_univ.prod C.domain_open).mem_nhds hp] with a ha
  exact (hillHminusDirichletColumn_eq_chart C a.2 ha.2 a.1).symm

theorem hillHminusDirichletColumn_initial (q : PeriodOneHminusOne) (lambda : ℂ) :
    extend (hillHminusDirichletColumn q lambda) 0 = 0 :=
  l2QuasiHillPosition_initial _ _ _

theorem hillHminusDirichletColumn_terminal (q : PeriodOneHminusOne) (lambda : ℂ) :
    extend (hillHminusDirichletColumn q lambda) 1 = hillHminusDirichlet q lambda :=
  ((hillHminusMiuraChartAt q).hillHminusDirichlet_eq_physicalPosition q (mem_hillHminusMiuraChartAt q) lambda).symm

theorem hillHminusDirichletColumn_ne_zero (q : PeriodOneHminusOne) (lambda : ℂ) :
    hillHminusDirichletColumn q lambda ≠ 0 :=
  (hillHminusMiuraChartAt q).physicalPosition_ne_zero q lambda (0,1) (by simp)

theorem hillHminusDirichletColumn_H1 (q : PeriodOneHminusOne) (lambda : ℂ) :
    AbsolutelyContinuousOnInterval (extend (hillHminusDirichletColumn q lambda)) 0 1 ∧
      MemLp (deriv (extend (hillHminusDirichletColumn q lambda))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have h := (hillHminusMiuraChartAt q).physicalSolution_scalar_H1 q lambda (0,1)
  exact ⟨h.1,h.2.1⟩

theorem hillHminusDirichletColumn_star_real (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (x : ℝ) :
    star (hillHminusDirichletColumn q x) = hillHminusDirichletColumn q x :=
  (hillHminusMiuraChartAt q).physicalPosition_dirichlet_star_real q (mem_hillHminusMiuraChartAt q) hr x

end NLS.KdV
