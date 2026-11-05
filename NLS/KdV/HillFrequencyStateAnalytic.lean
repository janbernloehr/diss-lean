import NLS.KdV.HillStateJointContinuity
import NLS.ZakharovShabat.L2FundamentalAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private def scalarStateZeroMap : Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) :=
  (constantUpperStateMap 0).compLeftContinuous ℂ (Icc (0 : ℝ) 1)

private def scalarStateFrequencyMap : Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) :=
  ((0 : (ℂ × ℂ) →L[ℂ] ℂ).prod ((-I) • ContinuousLinearMap.fst ℂ ℂ ℂ)).compLeftContinuous ℂ (Icc (0 : ℝ) 1)

private theorem scalarStateCurve_identity (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) :
    let Y := v.1 • l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0)+
      (I*v.2-z*v.1) • l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1)
    hillL2FrequencyStateCurve q z v=scalarStateZeroMap Y+z • scalarStateFrequencyMap Y := by
  dsimp only
  apply ContinuousMap.ext
  intro t
  rw [hillL2FrequencyStateCurve_apply]
  dsimp only [constantUpperInitialVector]
  have he := congrArg (fun Y : Curve (ℂ × ℂ) => Y t)
    (l2SolutionCurve_linearCombination (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z v))
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,constantUpperInitialVector] at he
  rw [he]
  let A := l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (1,0) t
  let B := l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (0,1) t
  apply Prod.ext
  · change (v.1*A.1+(I*v.2-z*v.1)*B.1)=
      (v.1*A.1+(I*v.2-z*v.1)*B.1)+z*0
    ring
  · change (-I*z)*(v.1*A.1+(I*v.2-z*v.1)*B.1)+(-I)*(v.1*A.2+(I*v.2-z*v.1)*B.2)=
      ((-I*0)*(v.1*A.1+(I*v.2-z*v.1)*B.1)+(-I)*(v.1*A.2+(I*v.2-z*v.1)*B.2))+
        z*((-I)*(v.1*A.1+(I*v.2-z*v.1)*B.1))
    ring

/-- The actual rough scalar Hill state is jointly analytic in frequency and source,
with values in the full uniform Banach space of state curves. -/
theorem analyticOnNhd_hillL2FrequencyStateCurve_joint (v : ℂ × ℂ) :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillL2FrequencyStateCurve p.2 p.1 v) univ := by
  let U : Coeff 2 → IntervalPairL2 := fun q => physicalRestrictionL2 (hillFirstOrderPotential q)
  have hU (q : Coeff 2) : AnalyticAt ℂ U q :=
    (physicalRestrictionL2CLM.analyticAt _).comp (f := hillFirstOrderPotential)
      (analyticAt_const.prod analyticAt_id.neg)
  have hsol (w : ℂ × ℂ) (p : ℂ × Coeff 2) :
      AnalyticAt ℂ (fun r : ℂ × Coeff 2 => l2SolutionCurve (U r.2) r.1 w) p :=
    (analyticOnNhd_l2SolutionCurve_joint w (p.1,U p.2) (mem_univ _)).comp
      (f := fun r : ℂ × Coeff 2 => (r.1,U r.2))
      (analyticAt_fst.prod ((hU p.2).comp (f := Prod.snd) analyticAt_snd))
  intro p _
  let Y : ℂ × Coeff 2 → Curve (ℂ × ℂ) := fun r =>
    v.1 • l2SolutionCurve (U r.2) r.1 (1,0)+(I*v.2-r.1*v.1) • l2SolutionCurve (U r.2) r.1 (0,1)
  have h1 : AnalyticAt ℂ (fun r : ℂ × Coeff 2 => v.1 • l2SolutionCurve (U r.2) r.1 (1,0)) p :=
    (hsol (1,0) p).const_smul (c := v.1)
  have hcoef : AnalyticAt ℂ (fun r : ℂ × Coeff 2 => I*v.2-r.1*v.1) p :=
    analyticAt_const.sub (analyticAt_fst.mul analyticAt_const)
  have h2 : AnalyticAt ℂ (fun r : ℂ × Coeff 2 => (I*v.2-r.1*v.1) • l2SolutionCurve (U r.2) r.1 (0,1)) p :=
    hcoef.smul (hsol (0,1) p)
  have hY : AnalyticAt ℂ Y p := h1.add h2
  have hG : AnalyticAt ℂ (fun r : ℂ × Coeff 2 => scalarStateZeroMap (Y r)+r.1 • scalarStateFrequencyMap (Y r)) p :=
    ((scalarStateZeroMap.analyticAt _).comp hY).add
      (analyticAt_fst.smul ((scalarStateFrequencyMap.analyticAt _).comp hY))
  apply hG.congr
  exact Eventually.of_forall (fun r => (scalarStateCurve_identity r.2 r.1 v).symm)

end NLS.KdV
