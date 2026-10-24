import NLS.ZakharovShabat.PhysicalWronskian
import NLS.ZakharovShabat.L2WholeLineIntegralEquation

/-! # Uniqueness of arbitrary locally AC whole-line physical solutions -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLS.ZakharovShabat

/-- Every locally AC solution of the original whole-line ODE is the
constructed fundamental solution with its own initial value. -/
theorem l2WholeLineSolution_unique_AC (u : IntervalPairL2) (z : ℂ) (F : ℝ → ℂ × ℂ)
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b)
    (hd : ∀ᵐ t : ℝ, HasDerivAt F (classicalODECoefficient (l2WholeLinePotential u t) z (F t)) t) :
    F = l2WholeLineSolution u z ![(F 0).1,(F 0).2] := by
  let c0 := l2WholeLineSolution u z ![1,0]
  let c1 := l2WholeLineSolution u z ![0,1]
  have hc0 := absolutelyContinuousOnInterval_l2WholeLineSolution u z ![1,0]
  have hc1 := absolutelyContinuousOnInterval_l2WholeLineSolution u z ![0,1]
  have hd0 := ae_hasDerivAt_l2WholeLineSolution u z ![1,0]
  have hd1 := ae_hasDerivAt_l2WholeLineSolution u z ![0,1]
  funext t
  have hdet : physicalWronskian (c0 t) (c1 t) = 1 := by
    simpa [c0,c1,physicalWronskian] using physicalWronskian_const_of_AC_solutions
      (l2WholeLinePotential u) c0 c1 z hc0 hc1 hd0 hd1 0 t
  have hfirst : physicalWronskian (F t) (c1 t) = (F 0).1 := by
    simpa [c1,physicalWronskian] using physicalWronskian_const_of_AC_solutions
      (l2WholeLinePotential u) F c1 z hac hc1 hd hd1 0 t
  have hsecond : physicalWronskian (c0 t) (F t) = (F 0).2 := by
    simpa [c0,physicalWronskian] using physicalWronskian_const_of_AC_solutions
      (l2WholeLinePotential u) c0 F z hc0 hac hd0 hd 0 t
  have he : F t = (F 0).1 • c0 t+(F 0).2 • c1 t := by
    simp only [physicalWronskian] at hdet hfirst hsecond
    apply Prod.ext
    · change (F t).1 = (F 0).1*(c0 t).1+(F 0).2*(c1 t).1
      linear_combination -(F t).1*hdet+(c0 t).1*hfirst+(c1 t).1*hsecond
    · change (F t).2 = (F 0).1*(c0 t).2+(F 0).2*(c1 t).2
      linear_combination -(F t).2*hdet+(c0 t).2*hfirst+(c1 t).2*hsecond
  rw [he]
  apply Prod.ext <;>
    simp [c0,c1,l2WholeLineSolution,Matrix.mulVec,dotProduct,Fin.sum_univ_two,mul_comm]

end NLS.ZakharovShabat
