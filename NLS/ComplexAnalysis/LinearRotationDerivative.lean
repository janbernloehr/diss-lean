import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # The derivative at zero of a bounded linear rotation formula -/
noncomputable section
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_linear_rotation_zero (z q v : E) :
    HasDerivAt (fun t : ℝ => z+((Real.cos t : ℂ)-1) • q+(Real.sin t : ℂ) • v) v 0 := by
  have hq := (((Real.hasDerivAt_cos 0).ofReal_comp.sub_const 1).smul_const q).const_add z
  have hv := (Real.hasDerivAt_sin 0).ofReal_comp.smul_const v
  convert! hq.add hv using 1
  simp


end NLS.ComplexAnalysis
