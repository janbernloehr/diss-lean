import NLS.ComplexAnalysis.SineIntegralKernelCorrection

/-! # The upper action bound from a semicircle correction

A uniform correction bound controls its exact sine-squared average with
the normalization constant one quarter.
-/

noncomputable section
open Set MeasureTheory
namespace NLS.ComplexAnalysis

/-- A uniform bound on the semicircle correction controls its exact action average. -/
theorem sine_correction_action_upper_bound (V : ℝ → ℝ) (hV : Continuous V)
    (E g : ℝ) (hE : ∀ θ ∈ Icc (0:ℝ) Real.pi, V θ ≤ E) :
    g^2/(2*Real.pi)*(∫ θ in (0:ℝ)..Real.pi, (Real.sin θ)^2*(1+V θ)) ≤
      g^2/4*(1+E) := by
  have hpoint (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) Real.pi) :
      (Real.sin θ)^2*(1+V θ) ≤ (1+E)*(Real.sin θ)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left (hE θ hθ) (sq_nonneg (Real.sin θ))]
  have hi := intervalIntegral.integral_mono_on (μ := volume) Real.pi_pos.le
    (((Real.continuous_sin.pow 2).mul (continuous_const.add hV)).intervalIntegrable _ _)
    ((continuous_const.mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _) hpoint
  change (∫ θ in (0:ℝ)..Real.pi, (Real.sin θ)^2*(1+V θ)) ≤
    (∫ θ in (0:ℝ)..Real.pi, (1+E)*(Real.sin θ)^2) at hi
  rw [intervalIntegral.integral_const_mul] at hi
  have hs : (∫ θ in (0:ℝ)..Real.pi, (Real.sin θ)^2) = Real.pi/2 := by simp [integral_sin_sq]
  rw [hs] at hi
  apply (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ g^2/(2*Real.pi))).trans_eq
  field_simp
  ring

end NLS.ComplexAnalysis
