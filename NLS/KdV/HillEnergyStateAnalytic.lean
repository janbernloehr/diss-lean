import NLS.KdV.HillFrequencyStateAnalytic
import NLS.KdV.HillEnergyStateShift

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual scalar state is jointly Banach analytic in energy and the rough source,
including energy zero. Exact constant shifts move the local square-root anchor to one. -/
theorem analyticOnNhd_hillL2EnergyStateCurve_joint (v : ℂ × ℂ) :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2EnergyStateCurve p.2 p.1 v) univ := by
  intro p _
  let c : ℂ := 1-p.1
  have hp : p.1+c=1 := by dsimp only [c];ring
  have hs : AnalyticAt ℂ Complex.sqrt (p.1+c) := by
    rw [hp]
    exact Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds (by simp [Complex.mem_slitPlane_iff]))
  let T : ℂ × Coeff 2 → ℂ × Coeff 2 := fun r => (Complex.sqrt (r.1+c),r.2+lp.single 2 0 c)
  have hT : AnalyticAt ℂ T p :=
    (hs.comp (f := fun r : ℂ × Coeff 2 => r.1+c) (analyticAt_fst.add analyticAt_const)).prod
      (analyticAt_snd.add analyticAt_const)
  have hF := (analyticOnNhd_hillL2FrequencyStateCurve_joint v (T p) (mem_univ _)).comp (f := T) hT
  apply hF.congr
  exact Eventually.of_forall (fun r => hillL2EnergyStateCurve_constant_shift r.2 r.1 c v)

end NLS.KdV
