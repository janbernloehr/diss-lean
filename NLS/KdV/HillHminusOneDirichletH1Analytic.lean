import NLS.KdV.HillHminusOneIntrinsicDirichletColumn
import NLS.MKdV.L2QuasiHillDerivativeClass

/-! # The intrinsic normalized H^-1 Dirichlet column is jointly H1 analytic

The graph consists of the full continuous position and its actual L2
classical derivative. Both coordinates are jointly entire in original
complex H^-1 potential and energy. The derivative class agrees with
every Miura chart, independently of all choices and shifts.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV NLS.Fourier
namespace NLS.KdV

def hillHminusDirichletDerivativeColumn (q : PeriodOneHminusOne) (lambda : ℂ) : IntervalL2 :=
  (hillHminusDirichletColumn_H1 q lambda).2.toLp (deriv (extend (hillHminusDirichletColumn q lambda)))

theorem hillHminusDirichletDerivativeColumn_representative (q : PeriodOneHminusOne) (lambda : ℂ) :
    hillHminusDirichletDerivativeColumn q lambda =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      deriv (extend (hillHminusDirichletColumn q lambda)) :=
  (hillHminusDirichletColumn_H1 q lambda).2.coeFn_toLp

theorem hillHminusDirichletDerivativeColumn_eq_chart (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (lambda : ℂ) :
    hillHminusDirichletDerivativeColumn q lambda =
      l2QuasiHillPositionDerivativeClass (C.physicalProfile q) (lambda+C.energyShift) (0,1) := by
  apply Lp.ext
  have h := hillHminusDirichletDerivativeColumn_representative q lambda
  rw [hillHminusDirichletColumn_eq_chart C q hq lambda] at h
  exact h.trans (l2QuasiHillPositionDerivativeClass_representative _ _ _).symm

theorem analyticOnNhd_hillHminusDirichletDerivativeColumn_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × PeriodOneHminusOne => hillHminusDirichletDerivativeColumn p.2 p.1) univ := by
  intro p _
  let C := hillHminusMiuraChartAt p.2
  have hp : p ∈ univ ×ˢ C.domain := ⟨mem_univ _,mem_hillHminusMiuraChartAt _⟩
  have hu := (unitL2SynthesisEquiv.toContinuousLinearEquiv.analyticAt _).comp
    (C.lift_analytic p.2 hp.2)
  have hpar : AnalyticAt ℂ (fun a : ℂ × PeriodOneHminusOne => (a.1+C.energyShift,C.physicalProfile a.2)) p :=
    (analyticAt_fst.add analyticAt_const).prod (hu.comp (f := Prod.snd) analyticAt_snd)
  have h := (analyticOnNhd_l2QuasiHillPositionDerivativeClass_joint (0,1) _ (mem_univ _)).comp
    (f := fun a : ℂ × PeriodOneHminusOne => (a.1+C.energyShift,C.physicalProfile a.2)) hpar
  apply h.congr
  filter_upwards [(isOpen_univ.prod C.domain_open).mem_nhds hp] with a ha
  exact (hillHminusDirichletDerivativeColumn_eq_chart C a.2 ha.2 a.1).symm

theorem analyticOnNhd_hillHminusDirichletH1Graph_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × PeriodOneHminusOne =>
      (hillHminusDirichletColumn p.2 p.1,hillHminusDirichletDerivativeColumn p.2 p.1)) univ :=
  fun p hp => (analyticOnNhd_hillHminusDirichletColumn_joint p hp).prod
    (analyticOnNhd_hillHminusDirichletDerivativeColumn_joint p hp)

end NLS.KdV
