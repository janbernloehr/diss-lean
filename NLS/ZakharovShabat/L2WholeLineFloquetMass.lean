import NLS.ZakharovShabat.L2WholeLineODEIntegrability
import NLS.ZakharovShabat.L2WholeLineTestDomain
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Positive periodic mass of actual unit-multiplier Floquet solutions -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Complex Matrix
namespace NLS.ZakharovShabat

/-- The continued fundamental matrix is invertible at every real time. -/
theorem isUnit_l2WholeLineFundamentalMatrix (u : IntervalPairL2) (z : ℂ) (t : ℝ) :
    IsUnit (l2WholeLineFundamentalMatrix u z t) := by
  apply IsUnit.mul
  · apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [det_l2FundamentalMatrix]
    exact isUnit_one
  · exact Units.isUnit _

/-- A nonzero initial vector never vanishes under the original physical propagation. -/
theorem l2WholeLineSolution_ne_zero (u : IntervalPairL2) (z : ℂ)
    (v : Fin 2 → ℂ) (hv : v ≠ 0) (t : ℝ) : l2WholeLineSolution u z v t ≠ 0 := by
  intro h
  apply hv
  apply Matrix.mulVec_injective_of_isUnit (isUnit_l2WholeLineFundamentalMatrix u z t)
  rw [Matrix.mulVec_zero]
  funext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- The pair solution retains the exact Floquet factor after every integer translation. -/
theorem l2WholeLineSolution_add_int_of_eigenvector (u : IntervalPairL2) (z μ : ℂ)
    (hμ : μ ≠ 0) (v : Fin 2 → ℂ) (hv : l2Monodromy u z *ᵥ v = μ • v)
    (t : ℝ) (n : ℤ) :
    l2WholeLineSolution u z v (t+n) = μ^n • l2WholeLineSolution u z v t := by
  simp only [l2WholeLineSolution,l2WholeLineFundamentalMatrix_add_int,
    ← Matrix.mulVec_mulVec,
    unit_matrix_zpow_mulVec_of_eigenvector (l2MonodromyUnit u z) μ hμ v hv n,
    Matrix.mulVec_smul,Pi.smul_apply,Prod.smul_mk]

/-- The squared Hermitian fibre norm of the actual physical solution. -/
def wholeLineSolutionMass (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) (t : ℝ) : ℝ :=
  ‖(WithLp.toLp 2 (l2WholeLineSolution u z v t) : WholeLineVector)‖ ^ 2

theorem continuous_wholeLineSolutionMass (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ) :
    Continuous (wholeLineSolutionMass u z v) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ ℂ ℂ).symm.continuous.comp
    (continuous_l2WholeLineSolution u z v)).norm.pow 2

/-- A unit Floquet multiplier makes the physical L2 density periodic. -/
theorem periodic_wholeLineSolutionMass (u : IntervalPairL2) (z μ : ℂ)
    (hμ : ‖μ‖ = 1) (v : Fin 2 → ℂ) (hv : l2Monodromy u z *ᵥ v = μ • v) :
    Function.Periodic (wholeLineSolutionMass u z v) 1 := by
  have hμ0 : μ ≠ 0 := by intro h; simp [h] at hμ
  intro t
  have he := l2WholeLineSolution_add_int_of_eigenvector u z μ hμ0 v hv t 1
  simp only [Int.cast_one,zpow_one] at he
  unfold wholeLineSolutionMass
  rw [he]
  change ‖μ • (WithLp.toLp 2 (l2WholeLineSolution u z v t) : WholeLineVector)‖ ^ 2 = _
  rw [norm_smul,hμ,one_mul]

/-- A nonzero physical solution has strictly positive mass on the unit period. -/
theorem wholeLineSolution_unit_mass_pos (u : IntervalPairL2) (z : ℂ)
    (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    0 < ∫ t in (0 : ℝ)..1, wholeLineSolutionMass u z v t := by
  apply intervalIntegral.intervalIntegral_pos_of_pos
    ((continuous_wholeLineSolutionMass u z v).intervalIntegrable 0 1) _ (by norm_num)
  intro t
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro h
  exact l2WholeLineSolution_ne_zero u z v hv t (congrArg WithLp.ofLp h)

/-- The L2 mass grows exactly linearly across any number of complete periods. -/
theorem wholeLineSolution_mass_nat_periods (u : IntervalPairL2) (z μ : ℂ)
    (hμ : ‖μ‖ = 1) (v : Fin 2 → ℂ) (hv : l2Monodromy u z *ᵥ v = μ • v) (n : ℕ) :
    (∫ t in (0 : ℝ)..(n : ℝ), wholeLineSolutionMass u z v t) =
      (n : ℝ) * ∫ t in (0 : ℝ)..1, wholeLineSolutionMass u z v t := by
  have h := (periodic_wholeLineSolutionMass u z μ hμ v hv).intervalIntegral_add_zsmul_eq (n : ℤ) 0
    ((continuous_wholeLineSolutionMass u z v).intervalIntegrable)
  simpa only [zsmul_eq_mul,Int.cast_natCast,mul_one,zero_add] using h

end NLS.ZakharovShabat
