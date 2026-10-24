import NLS.ZakharovShabat.L2WholeLineLocalIntegrability
import NLS.ZakharovShabat.L2WholeLineFloquetBound

/-! # Local integrability of the actual whole-line physical equation -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Complex
namespace NLS.ZakharovShabat

/-- The physical pair solution is continuous on the whole real line. -/
theorem continuous_l2WholeLineSolution (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) :
    Continuous (l2WholeLineSolution u z v) := by
  have h := continuous_matrixCurve_mulVec _ (continuous_l2WholeLineFundamentalMatrix u z) v
  exact ((continuous_apply 0).comp h).prodMk ((continuous_apply 1).comp h)

theorem locallyIntegrable_l2WholeLinePotential_fst (u : IntervalPairL2) :
    LocallyIntegrable (fun t => (l2WholeLinePotential u t).1) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact (memLp_l2WholeLinePotential_on_compact u hK).fst.integrable (by norm_num)

theorem locallyIntegrable_l2WholeLinePotential_snd (u : IntervalPairL2) :
    LocallyIntegrable (fun t => (l2WholeLinePotential u t).2) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact (memLp_l2WholeLinePotential_on_compact u hK).snd.integrable (by norm_num)

/-- The actual differential-equation right-hand side is locally integrable,
without assuming the potential or solution is globally L2. -/
theorem locallyIntegrable_l2WholeLineODE (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) :
    LocallyIntegrable (fun t => classicalODECoefficient (l2WholeLinePotential u t) z
      (l2WholeLineSolution u z v t)) volume := by
  have hc := continuous_l2WholeLineSolution u z v
  have hp1 := LocallyIntegrable.mul_continuous hc.snd (locallyIntegrable_l2WholeLinePotential_fst u)
  have hp2 := LocallyIntegrable.mul_continuous hc.fst (locallyIntegrable_l2WholeLinePotential_snd u)
  have ha := ((continuous_const (y := -I*z)).mul hc.fst).locallyIntegrable (μ := volume)
    |>.add (hp1.smul I)
  have hb := (hp2.smul (-I)).add (((continuous_const (y := I*z)).mul hc.snd).locallyIntegrable (μ := volume))
  apply locallyIntegrable_iff.mpr
  intro K hK
  simpa only [classicalODECoefficient_apply,mul_assoc,Pi.smul_apply,smul_eq_mul,Pi.add_apply,Pi.mul_apply,IntegrableOn]
    using! (ha.integrableOn_isCompact hK).prodMk (hb.integrableOn_isCompact hK)

/-- Its integral is defined over every finite interval of the real line. -/
theorem intervalIntegrable_l2WholeLineODE (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) (a b : ℝ) :
    IntervalIntegrable (fun t => classicalODECoefficient (l2WholeLinePotential u t) z
      (l2WholeLineSolution u z v t)) volume a b := by
  exact intervalIntegrable_iff.mpr
    (((locallyIntegrable_l2WholeLineODE u z v).integrableOn_isCompact isCompact_uIcc).mono_set
      uIoc_subset_uIcc)

end NLS.ZakharovShabat
