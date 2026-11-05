import NLS.KdV.HillHminusDirichletCharts
import NLS.MKdV.QuasiHillL2NormingTrace

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.MKdV
namespace NLS.KdV

namespace HillHminusMiuraChart

/-- The actual terminal quasi-derivative on a chosen actual energy branch.
At a characteristic zero this is the physical derivative-one multiplier. -/
def dirichletTerminal (C : HillHminusMiuraChart) (a : PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) : ℂ :=
  quasiHillL2DirichletTerminal (C.lift q) (a q+C.energyShift)

theorem analyticAt_dirichletTerminal (C : HillHminusMiuraChart)
    (a : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) (hq : q∈C.domain)
    (ha : AnalyticAt ℂ a q) : AnalyticAt ℂ (C.dirichletTerminal a) q :=
  (analyticOnNhd_quasiHillL2DirichletTerminal_joint
    (a q+C.energyShift,C.lift q) (mem_univ _)).comp
      (f := fun p => (a p+C.energyShift,C.lift p))
      ((ha.add analyticAt_const).prod (C.lift_analytic q hq))

theorem dirichletTerminal_ne_zero_of_root (C : HillHminusMiuraChart)
    (a : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) (hq : q∈C.domain)
    (hz : hillHminusDirichlet q (a q)=0) : C.dirichletTerminal a q≠0 := by
  apply quasiHillL2DirichletTerminal_ne_zero
  rw [hillHminusDirichlet_eq_chart C q hq] at hz
  exact hz

/-- At any original complex Hilbert characteristic zero the endpoint gauge
vanishes, so the chart multiplier is the literal original physical slope. -/
theorem dirichletTerminal_eq_hillL2_of_root (C : HillHminusMiuraChart)
    (a : PeriodOneHminusOne → ℂ) (q : Coeff 2)
    (hq : periodOneL2Inclusion q∈C.domain)
    (hz : hillHminusDirichlet (periodOneL2Inclusion q) (a (periodOneL2Inclusion q))=0) :
    C.dirichletTerminal a (periodOneL2Inclusion q)=
      hillL2DirichletSlope (Coeff.periodDouble q) (a (periodOneL2Inclusion q)) := by
  rw [dirichletTerminal,←hillL2DirichletTerminal_eq_slope]
  apply quasiHillL2DirichletTerminal_eq_hillL2_of_shifted_root
  · rw [map_add]
    exact C.image _ hq
  · rw [hillHminusDirichlet_eq_chart C _ hq] at hz
    exact hz

/-- The chart terminal multiplier has the exact original physical slope on
all original even rough characteristic zeros, with no reality requirement. -/
theorem dirichletTerminal_original_source (C : HillHminusMiuraChart)
    (a : PeriodOneHminusOne → ℂ) (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hC : hillOriginalHminusSource q∈C.domain)
    (hz : hillHminusDirichlet (hillOriginalHminusSource q) (a (hillOriginalHminusSource q))=0) :
    C.dirichletTerminal a (hillOriginalHminusSource q)=
      hillL2DirichletSlope (SpectralWeight.one.toCoeff q) (a (hillOriginalHminusSource q)) := by
  have h := C.dirichletTerminal_eq_hillL2_of_root a
    (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q)) hC hz
  rw [hillPeriodDouble_unitSample _ hq] at h
  exact h

/-- The actual trace equals T plus its inverse at a root, for the genuine
terminal multiplier T of this chart. -/
theorem discriminant_eq_dirichletTerminal_inv_add (C : HillHminusMiuraChart)
    (a : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) (hq : q∈C.domain)
    (hz : hillHminusDirichlet q (a q)=0) :
    hillHminusDiscriminant q (a q)=(C.dirichletTerminal a q)⁻¹+C.dirichletTerminal a q := by
  rw [hillHminusDiscriminant_eq_chart C q hq]
  apply hillMiuraL2Discriminant_of_dirichlet_root
  rw [hillHminusDirichlet_eq_chart C q hq] at hz
  exact hz

end HillHminusMiuraChart
end NLS.KdV
