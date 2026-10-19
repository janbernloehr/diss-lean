import NLS.ZakharovShabat.ClassicalScalarForcingFreeComparison

/-! # Additivity of the actual forced solution

The zero-initial forced kernel solution and the scalar forcing embedding preserve addition.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The actual zero-initial forced solution preserves addition of forcing
curves throughout the physical interval. -/
theorem classicalForcedKernelSolution_add_forcing
    (Φ g h : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0:ℝ) 1) :
    classicalForcedKernelSolution Φ (g+h) z t =
      classicalForcedKernelSolution Φ g z t+classicalForcedKernelSolution Φ h z t := by
  rw [classicalForcedKernelSolution_eq_forcedSolution,
    classicalForcedKernelSolution_eq_forcedSolution,classicalForcedKernelSolution_eq_forcedSolution,
    forcedSolution_coe,forcedSolution_coe,forcedSolution_coe]
  simp only [forcedSolutionCurve,
    show ContinuousMap.const (Icc (0:ℝ) 1) (0:ℂ × ℂ) = 0 from rfl,
    zero_add,map_add,ContinuousMap.add_apply]

/-- Scalar lower forcing respects the same additive decomposition. -/
theorem classicalScalarForcing_add (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    classicalScalarForcing (f+g) (hf.add hg) = classicalScalarForcing f hf+classicalScalarForcing g hg := by
  ext x <;> simp [classicalScalarForcing]

end NLS.ZakharovShabat
