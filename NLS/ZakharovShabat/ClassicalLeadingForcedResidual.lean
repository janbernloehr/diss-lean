import NLS.ZakharovShabat.ClassicalIntegralResidualStability

/-! # Subtracting the leading forced correction

The remaining actual solution error is controlled by the L1 difference of the two residuals.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Subtracting an explicit forced correction leaves only the difference
of the two residuals in the actual solution error. -/
theorem norm_sub_classicalSolution_sub_forced_le_integral_residual
    (Φ g h : Curve (ℂ × ℂ)) (z : ℂ) (H : ℝ) (hz : |z.im| ≤ H)
    (u : ℝ → ℂ × ℂ) (hu : Continuous u)
    (hd : ∀ t : Icc (0:ℝ) 1, HasDerivAt u (classicalODECoefficient (Φ t) z (u t)+g t) t)
    (t : Icc (0:ℝ) 1) :
    ‖u t-classicalSolution Φ z (u 0) t-classicalForcedKernelSolution Φ h z t‖ ≤
      4*(Real.exp (‖Φ‖+H))^2*(∫ x in (0:ℝ)..1, ‖extend (g-h) x‖) := by
  let v (x : ℝ) := u x-classicalForcedKernelSolution Φ h z x
  have hv : Continuous v := hu.sub (continuous_classicalForcedKernelSolution Φ h z)
  have hvd (x : Icc (0:ℝ) 1) :
      HasDerivAt v (classicalODECoefficient (Φ x) z (v x)+(g-h) x) x := by
    have hdv := (hd x).sub (hasDerivAt_classicalForcedKernelSolution Φ h z x)
    convert! hdv using 1
    dsimp only [v]
    simp only [map_sub,ContinuousMap.sub_apply]
    abel
  have he := norm_sub_classicalSolution_strip_le_integral_residual Φ (g-h) z H hz v hv hvd t
  simpa only [v,classicalForcedKernelSolution_zero,sub_zero,sub_right_comm] using he

end NLS.ZakharovShabat
