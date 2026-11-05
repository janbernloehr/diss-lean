import NLS.FunctionalAnalysis.LinearVolterra
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Every continuous unit curve has all finite and infinite Lp bounds -/
noncomputable section
open Set MeasureTheory NLS.LinearVolterra
open scoped ENNReal
namespace NLS.FunctionalAnalysis

theorem memLp_unitCurve_extend (p : ℝ≥0∞) (f : Curve ℂ) :
    MemLp (NLS.LinearVolterra.extend f) p (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply MemLp.of_bound (continuous_extend f).aestronglyMeasurable ‖f‖
  exact Filter.Eventually.of_forall (fun x => ContinuousMap.norm_coe_le_norm f (projIcc 0 1 (by norm_num) x))

end NLS.FunctionalAnalysis
