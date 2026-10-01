import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Gronwall with a continuous variable coefficient

A strict exponential comparison with a positive perturbation handles a
vanishing initial vector as well. Letting the perturbation tend to zero
gives a bound by the integral of the actual coefficient, rather than its
supremum on the interval.
-/

noncomputable section
open Set MeasureTheory
namespace NLS.FunctionalAnalysis

/-- A continuous variable coefficient in the derivative bound gives an
exponential bound using its integral. No sign assumption on the coefficient
or nonvanishing assumption on the initial vector is needed. -/
theorem norm_le_exp_integral_of_norm_deriv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {α : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (hα : Continuous α)
    (hbound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ α x * ‖f x‖) :
    ∀ x ∈ Icc a b, ‖f x‖ ≤ ‖f a‖ * Real.exp (∫ s in a..x, α s) := by
  have H : ∀ x ∈ Icc a b, ∀ ε ∈ Ioi (0 : ℝ),
      ‖f x‖ ≤ (‖f a‖ + ε) * Real.exp ((∫ s in a..x, α s) + ε * (x-a)) := by
    intro x hx ε hε
    change 0 < ε at hε
    let B : ℝ → ℝ := fun y =>
      (‖f a‖ + ε) * Real.exp ((∫ s in a..y, α s) + ε * (y-a))
    have hB (y : ℝ) : HasDerivAt B ((α y + ε) * B y) y := by
      have hprimitive := intervalIntegral.integral_hasDerivAt_right
        (hα.intervalIntegrable a y)
        hα.stronglyMeasurable.stronglyMeasurableAtFilter hα.continuousAt
      have hlinear := ((hasDerivAt_id y).sub_const a).const_mul ε
      convert! ((hprimitive.add hlinear).exp.const_mul (‖f a‖ + ε)) using 1
      dsimp [B]
      ring
    apply image_norm_le_of_norm_deriv_right_lt_deriv_boundary hf hf' (B' := fun y => (α y+ε)*B y)
      (by dsimp [B]; simpa using hε.le) hB _ hx
    intro y hy heq
    have hpos : 0 < B y := by dsimp [B]; positivity
    calc
      ‖f' y‖ ≤ α y * ‖f y‖ := hbound y hy
      _ = α y * B y := by rw [heq]
      _ < (α y + ε) * B y := by nlinarith
  intro x hx
  have hc : Continuous (fun ε : ℝ =>
      (‖f a‖ + ε) * Real.exp ((∫ s in a..x, α s) + ε * (x-a))) := by fun_prop
  have h := continuousWithinAt_const.closure_le
    (show (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) by simp) hc.continuousWithinAt (H x hx)
  simpa using h

end NLS.FunctionalAnalysis
