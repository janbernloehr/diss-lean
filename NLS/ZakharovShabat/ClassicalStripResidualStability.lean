import NLS.ZakharovShabat.ClassicalResidualStability

/-! # Residual stability on complex spectral strips

The actual solution error is controlled uniformly across each horizontal complex spectral strip.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Residual stability uniformly on a horizontal complex spectral strip. -/
theorem norm_sub_classicalSolution_strip_le_of_residual
    (Φ g : Curve (ℂ × ℂ)) (z : ℂ) (H : ℝ) (hz : |z.im| ≤ H)
    (u : ℝ → ℂ × ℂ) (hu : Continuous u)
    (hd : ∀ t : Icc (0 : ℝ) 1, HasDerivAt u (classicalODECoefficient (Φ t) z (u t)+g t) t)
    (D : ℝ) (hD : 0 ≤ D) (hg : ∀ t : Icc (0 : ℝ) 1, ‖g t‖ ≤ D) (t : Icc (0 : ℝ) 1) :
    ‖u t-classicalSolution Φ z (u 0) t‖ ≤ 4*(Real.exp (‖Φ‖+H))^2*D := by
  apply norm_sub_classicalSolution_le_of_residual Φ g z u hu hd _ D (Real.exp_pos _).le hD _ hg t
  intro v hv s
  apply (norm_classicalSolution_le_exp_im Φ z v s).trans
  calc
    _ ≤ 1*Real.exp (‖Φ‖+H) := by
      apply mul_le_mul hv (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le zero_le_one
      calc
        _ ≤ |z.im|+‖Φ‖ := mul_le_of_le_one_right (by positivity) s.property.2
        _ ≤ _ := by linarith
    _ = _ := one_mul _

end NLS.ZakharovShabat
