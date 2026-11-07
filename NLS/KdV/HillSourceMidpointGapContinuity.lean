import NLS.KdV.HillCanonicalZeroSequencePeriods
import NLS.ZakharovShabat.SourcePeriodicMidpointGapContinuity

/-! Native source continuity of the actual Miura frequency midpoints
and gaps at every physical real source, in the original topology. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem sourcePsi_real (P : HillProductEquationPatch) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := by
  let B := P.parent.parent.miuraBall.actionBall
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  exact (hillMiuraRealSource u).property

theorem continuousAt_source_frequency_midpoint (P : HillProductEquationPatch) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (k : ℤ) :
    ContinuousAt (fun y => sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) k) q := by
  have hreal := P.sourcePsi_real q hq hr
  have hL := (continuousAt_canonicalPeriodicLeft_periodOne_of_realType (by norm_num) (by norm_num) (P.sourcePsi q) hreal k).comp
    (P.analytic_sourcePsi q hq).continuousAt
  have hR := (continuousAt_canonicalPeriodicRight_periodOne_of_realType (by norm_num) (by norm_num) (P.sourcePsi q) hreal k).comp
    (P.analytic_sourcePsi q hq).continuousAt
  exact (hL.add hR).div_const (2:ℂ)

theorem continuousAt_source_frequency_gap (P : HillProductEquationPatch) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (k : ℤ) :
    ContinuousAt (fun y => sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi y) k) q := by
  have hreal := P.sourcePsi_real q hq hr
  have hL := (continuousAt_canonicalPeriodicLeft_periodOne_of_realType (by norm_num) (by norm_num) (P.sourcePsi q) hreal k).comp
    (P.analytic_sourcePsi q hq).continuousAt
  have hR := (continuousAt_canonicalPeriodicRight_periodOne_of_realType (by norm_num) (by norm_num) (P.sourcePsi q) hreal k).comp
    (P.analytic_sourcePsi q hq).continuousAt
  convert hR.sub hL using 1
  funext y
  rw [sourcePeriodicGapDisplacement_apply]
  rfl

end NLS.KdV.HillProductEquationPatch
