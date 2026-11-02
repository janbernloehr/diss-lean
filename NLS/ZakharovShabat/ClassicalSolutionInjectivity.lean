import NLS.ZakharovShabat.ClassicalBoundaryDeterminants
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! # Injectivity of the constructed classical state propagation

The actual fundamental matrix has determinant one throughout the unit
interval. Its propagated state therefore determines the initial vector,
including at every interior point and at zero spectral parameter.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Matrix NLS.LinearVolterra
namespace NLS.ZakharovShabat

theorem classicalSolution_injective_initial (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0 : ℝ) 1) : Function.Injective (fun v => classicalSolution φ z v t) := by
  intro v w he
  change classicalSolution φ z v t = classicalSolution φ z w t at he
  have hi := Matrix.mulVec_injective_of_det_ne_zero
    (M := classicalFundamentalMatrix φ z t) (by rw [det_classicalFundamentalMatrix]; norm_num)
  have hvw : ![v.1,v.2] = ![w.1,w.2] := hi (by
    rw [classicalFundamentalMatrix_mulVec φ z _ t,classicalFundamentalMatrix_mulVec φ z _ t]
    change ![(classicalSolution φ z v t).1,(classicalSolution φ z v t).2] =
      ![(classicalSolution φ z w t).1,(classicalSolution φ z w t).2]
    rw [he])
  exact Prod.ext (congrFun hvw 0) (congrFun hvw 1)

/-- A nonzero initial vector cannot propagate to a zero state anywhere
on the whole closed interval. -/
theorem classicalSolution_eq_zero_imp_initial_eq_zero (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) (he : classicalSolution φ z v t = 0) : v = 0 := by
  have hi := Matrix.mulVec_injective_of_det_ne_zero
    (M := classicalFundamentalMatrix φ z t) (by rw [det_classicalFundamentalMatrix]; norm_num)
  have hv : ![v.1,v.2] = 0 := hi (by
    rw [Matrix.mulVec_zero,classicalFundamentalMatrix_mulVec φ z _ t]
    change ![(classicalSolution φ z v t).1,(classicalSolution φ z v t).2] = 0
    rw [he]
    simp)
  exact Prod.ext (congrFun hv 0) (congrFun hv 1)

end NLS.ZakharovShabat
