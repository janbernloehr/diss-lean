import NLS.FunctionalAnalysis.IntegralAbsoluteContinuity
import NLS.ZakharovShabat.L2WholeLineSolutionPeriods

/-! # Absolute continuity of the actual physical solution on each closed period

The original Volterra integral identity supplies absolute continuity.
The proof does not infer it merely from an almost-everywhere derivative.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Matrix
open NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Every original physical L2 solution is absolutely continuous on the
closed unit interval, by its actual Banach-valued Volterra representation. -/
theorem absolutelyContinuousOnInterval_l2SolutionCurve
    (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    AbsolutelyContinuousOnInterval (extend (l2SolutionCurve u z v)) 0 1 := by
  have hi := intervalIntegrable_l2ODECoefficient u z (l2SolutionCurve u z v)
    (⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
  have ha := absolutelyContinuousOnInterval_const_add
    (absolutelyContinuousOnInterval_integral hi (by simp : (0 : ℝ) ∈ uIcc 0 1)) v
  apply absolutelyContinuousOnInterval_congr ha
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ ht'] using (l2SolutionCurve_eq_integral u z v ⟨t,ht'⟩).symm

/-- Every positive or negative closed period has the actual absolute
continuity property in its local unit-interval coordinate. -/
theorem absolutelyContinuousOnInterval_l2WholeLineSolution_period
    (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) (n : ℤ) :
    AbsolutelyContinuousOnInterval (fun s : ℝ => l2WholeLineSolution u z v (s+n)) 0 1 := by
  let w : Fin 2 → ℂ := (↑((l2MonodromyUnit u z)^n) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v
  apply absolutelyContinuousOnInterval_congr
    (absolutelyContinuousOnInterval_l2SolutionCurve u z (w 0,w 1))
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa using hs
  simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ hs'] using (l2WholeLineSolution_on_period u z v n ⟨s,hs'⟩).symm

end NLS.ZakharovShabat
