import NLS.KdV.HillHminusOneWeakFormCharts

/-! # The intrinsic weak Hill form at every complex H^-1 potential

For H1 curves whose product has matching endpoints, every analytic Miura
chart gives exactly this same form. It agrees with the physical L2 Hill
form on L2 potentials and is entire in the original complex H^-1 norm.
The definition outside these admissible curve pairs has no assertion of
chart independence.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

def hillHminusWeakForm (q : PeriodOneHminusOne) (y φ : Curve ℂ) : ℂ :=
  shiftedMiuraWeakForm ((hillHminusMiuraChartAt q).physicalProfile q)
    (hillHminusMiuraChartAt q).energyShift y φ

/-- Independence from lift branch and constant shift for the full
natural class of periodic-product H1 test pairs. -/
theorem hillHminusWeakForm_eq_chart (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (y φ : Curve ℂ) (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend y 1*extend φ 1 = extend y 0*extend φ 0) :
    hillHminusWeakForm q y φ = shiftedMiuraWeakForm (C.physicalProfile q) C.energyShift y φ :=
  (hillHminusMiuraChartAt q).weakForm_eqOn_overlap C y φ hy hφ hy₂ hφ₂ hend
    ⟨mem_hillHminusMiuraChartAt q,hq⟩

theorem analyticOnNhd_hillHminusWeakForm (y φ : Curve ℂ)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend y 1*extend φ 1 = extend y 0*extend φ 0) :
    AnalyticOnNhd ℂ (fun q => hillHminusWeakForm q y φ) univ := by
  intro q _
  let C := hillHminusMiuraChartAt q
  have hq : q ∈ C.domain := mem_hillHminusMiuraChartAt q
  apply (C.analyticAt_weakForm q hq y φ hy₂ hφ₂).congr
  filter_upwards [C.domain_open.mem_nhds hq] with p hp
  exact (hillHminusWeakForm_eq_chart C p hp y φ hy hφ hy₂ hφ₂ hend).symm

/-- The intrinsic form has the ordinary physical L2 potential term on
every L2 input, without imposing mean zero or a reality condition. -/
theorem hillHminusWeakForm_eq_physicalL2 (p : Coeff 2) (y φ : Curve ℂ)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend y 1*extend φ 1 = extend y 0*extend φ 0) :
    hillHminusWeakForm (periodOneL2Inclusion p) y φ = physicalL2HillWeakForm (unitL2SynthesisEquiv p) y φ :=
  (hillHminusMiuraChartAt (periodOneL2Inclusion p)).weakForm_eq_physicalL2 p
    (mem_hillHminusMiuraChartAt _) y φ hy hφ hy₂ hφ₂ hend

end NLS.KdV
