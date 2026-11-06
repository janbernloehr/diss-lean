import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Basic

/-! # The clockwise physical Cartesian action rotation -/
noncomputable section
namespace NLS.ComplexAnalysis

def cartesianPlaneRotation (t : ℝ) (z : ℂ × ℂ) : ℂ × ℂ :=
  ((Real.cos t : ℂ)*z.1+(Real.sin t : ℂ)*z.2,
   -(Real.sin t : ℂ)*z.1+(Real.cos t : ℂ)*z.2)

@[simp] theorem cartesianPlaneRotation_zero (z : ℂ × ℂ) : cartesianPlaneRotation 0 z = z := by
  simp [cartesianPlaneRotation]

/-- Reversing the second coordinate changes the usual NLS rotation to
the physical Gardner orientation, with any common scalar multiplier. -/
theorem cartesianPlaneRotation_scaled_reflection (r : ℂ) (t : ℝ) (z : ℂ × ℂ) :
    (r*(cartesianPlaneRotation (-t) z).1,-(r*(cartesianPlaneRotation (-t) z).2)) =
      cartesianPlaneRotation t (r*z.1,-(r*z.2)) := by
  simp only [cartesianPlaneRotation,Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
  apply Prod.ext <;> dsimp only <;> ring

theorem cartesianPlaneRotation_radius (t : ℝ) (z : ℂ × ℂ) :
    (cartesianPlaneRotation t z).1^2+(cartesianPlaneRotation t z).2^2 = z.1^2+z.2^2 := by
  have ht : (Real.sin t : ℂ)^2+(Real.cos t : ℂ)^2 = 1 := by exact_mod_cast Real.sin_sq_add_cos_sq t
  dsimp only [cartesianPlaneRotation]
  linear_combination (z.1^2+z.2^2)*ht

theorem hasDerivAt_cartesianPlaneRotation (z : ℂ × ℂ) (t : ℝ) :
    HasDerivAt (fun r => cartesianPlaneRotation r z)
      ((cartesianPlaneRotation t z).2,-(cartesianPlaneRotation t z).1) t := by
  have hx := ((Real.hasDerivAt_cos t).ofReal_comp.mul_const z.1).add
    ((Real.hasDerivAt_sin t).ofReal_comp.mul_const z.2)
  have hy := ((Real.hasDerivAt_sin t).ofReal_comp.neg.mul_const z.1).add
    ((Real.hasDerivAt_cos t).ofReal_comp.mul_const z.2)
  simpa only [cartesianPlaneRotation,Complex.ofReal_neg,neg_add,neg_mul,Pi.add_apply,Pi.neg_apply] using hx.prodMk hy

end NLS.ComplexAnalysis
