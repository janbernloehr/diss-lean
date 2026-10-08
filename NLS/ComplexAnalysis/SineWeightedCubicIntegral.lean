import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # A cubic lower bound for a nonnegative cosine-coordinate profile -/
noncomputable section
open Set MeasureTheory
namespace NLS.ComplexAnalysis

/-- Jensen's cubic inequality for the sine measure, whose total mass is two. -/
theorem sine_integral_cube_le (f : ℝ → ℝ) (hf : Continuous f)
    (hpos : ∀ x ∈ Icc (0:ℝ) Real.pi, 0 ≤ f x) :
    (∫ x in (0:ℝ)..Real.pi, Real.sin x*f x)^3 ≤
      4*(∫ x in (0:ℝ)..Real.pi, Real.sin x*(f x)^3) := by
  let c := (∫ x in (0:ℝ)..Real.pi, Real.sin x*f x)/2
  have hc : 0 ≤ c := by
    apply div_nonneg _ (by norm_num)
    exact intervalIntegral.integral_nonneg Real.pi_pos.le
      (fun x hx => mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2) (hpos x hx))
  have hpoint (x : ℝ) (hx : x ∈ Icc (0:ℝ) Real.pi) :
      Real.sin x*(3*c^2*f x-2*c^3) ≤ Real.sin x*(f x)^3 := by
    apply mul_le_mul_of_nonneg_left _ (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)
    nlinarith [mul_nonneg (sq_nonneg (f x-c)) (show 0 ≤ f x+2*c by linarith [hpos x hx])]
  have hi := intervalIntegral.integral_mono_on (μ := volume) Real.pi_pos.le
    ((Real.continuous_sin.mul ((continuous_const.mul hf).sub continuous_const)).intervalIntegrable _ _)
    ((Real.continuous_sin.mul (hf.pow 3)).intervalIntegrable _ _) hpoint
  have he : (fun x : ℝ => Real.sin x*(3*c^2*f x-2*c^3)) =
      (fun x : ℝ => (3*c^2)*(Real.sin x*f x)-(2*c^3)*Real.sin x) := by funext x; ring
  change (∫ x in (0:ℝ)..Real.pi, Real.sin x*(3*c^2*f x-2*c^3)) ≤
    (∫ x in (0:ℝ)..Real.pi, Real.sin x*(f x)^3) at hi
  have hi₁ : IntervalIntegrable (fun x : ℝ => (3*c^2)*(Real.sin x*f x)) volume 0 Real.pi :=
    (Real.continuous_sin.mul hf).intervalIntegrable _ _ |>.const_mul _
  have hi₂ : IntervalIntegrable (fun x : ℝ => (2*c^3)*Real.sin x) volume 0 Real.pi :=
    Real.continuous_sin.intervalIntegrable _ _ |>.const_mul _
  rw [he,intervalIntegral.integral_sub hi₁ hi₂,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    integral_sin,Real.cos_zero,Real.cos_pi] at hi
  dsimp [c] at hi
  nlinarith

end NLS.ComplexAnalysis
