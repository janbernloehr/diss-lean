import NLS.ZakharovShabat.ClassicalParityEigenvectors
import NLS.ZakharovShabat.ClassicalRemainderDerivativeBound

/-! # Time regularity of the actual fundamental-solution error

The ODE solution and free propagator are C¹ on the real line. Their
difference and every bounded linear observation therefore have actual
continuous derivatives, including at the physical interval endpoints.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The explicit free vector is continuously differentiable in time. -/
theorem contDiff_classicalFreeVector (z : ℂ) (v : ℂ × ℂ) :
    ContDiff ℝ 1 (classicalFreeVector z v) := by
  unfold classicalFreeVector
  have hc : ContDiff ℝ 1 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

/-- The actual error inherits global C¹ time regularity from the two solutions. -/
theorem contDiff_classicalSolutionRemainder (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    ContDiff ℝ 1 (classicalSolutionRemainder φ z v) :=
  (contDiff_classicalSolution φ z v).sub (contDiff_classicalFreeVector z v)

/-- Every bounded real-linear scalar observation has a continuous time derivative. -/
theorem contDiff_classicalRemainder_observation
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) :
    ContDiff ℝ 1 (fun t => L (classicalSolutionRemainder φ z v t)) :=
  L.contDiff.comp (contDiff_classicalSolutionRemainder φ z v)

/-- Differentiating an observation commutes with its fixed bounded linear map. -/
theorem deriv_classicalRemainder_observation
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) (t : ℝ) :
    deriv (fun s => L (classicalSolutionRemainder φ z v s)) t =
      L (deriv (classicalSolutionRemainder φ z v) t) := by
  have hd := (contDiff_one_iff_deriv.mp (contDiff_classicalSolutionRemainder φ z v)).1 t
  exact (L.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv

end NLS.ZakharovShabat
