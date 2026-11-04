import NLS.ZakharovShabat.L2FundamentalInitialValue
import Mathlib.Tactic

/-! # The actual physical L2 solution never vanishes for nonzero initial data. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate ENNReal
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

theorem l2SolutionCurve_ne_zero (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (hv : v≠0) (t : Icc (0 : ℝ) 1) : l2SolutionCurve u z v t≠0 := by
  intro hz
  have hu : IsUnit (l2FundamentalMatrix u z t) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [det_l2FundamentalMatrix]
    exact isUnit_one
  have ht : l2SolutionCurve u z v t = v.1 • l2SolutionCurve u z (1,0) t+v.2 • l2SolutionCurve u z (0,1) t := by
    simpa only [ContinuousMap.add_apply,ContinuousMap.smul_apply] using
      congrArg (fun f : Curve (ℂ × ℂ) => f t) (l2SolutionCurve_linearCombination u z v)
  have hy : v.1 • l2SolutionCurve u z (1,0) t+v.2 • l2SolutionCurve u z (0,1) t=0 := ht.symm.trans hz
  have hm : l2FundamentalMatrix u z t *ᵥ (![v.1,v.2] : Fin 2 → ℂ) =
      l2FundamentalMatrix u z t *ᵥ (0 : Fin 2 → ℂ) := by
    rw [Matrix.mulVec_zero]
    funext i
    fin_cases i
    · have hh := congrArg Prod.fst hy
      simpa [l2FundamentalMatrix,Matrix.mulVec,Fin.sum_univ_two,smul_eq_mul,mul_comm] using hh
    · have hh := congrArg Prod.snd hy
      simpa [l2FundamentalMatrix,Matrix.mulVec,Fin.sum_univ_two,smul_eq_mul,mul_comm] using hh
  have hh := Matrix.mulVec_injective_of_isUnit hu hm
  apply hv
  exact Prod.ext (congrFun hh 0) (congrFun hh 1)

end NLS.ZakharovShabat
