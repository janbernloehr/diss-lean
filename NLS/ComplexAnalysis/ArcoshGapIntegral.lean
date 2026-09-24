import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# An arcosh endpoint identity for an open spectral gap

When a real function exceeds one in the interior of an interval but
equals one at both endpoints, the integral of its derivative divided
by `√(f² - 1)` vanishes. This is the real-calculus step in the
open-gap part of Lemma 10.11(ii).
-/

noncomputable section
open Set MeasureTheory intervalIntegral
namespace NLS.ComplexAnalysis

/-- The arcosh derivative has zero integral between equal gap levels.
Endpoint singularities are allowed as long as the derivative is
interval-integrable. -/
theorem integral_deriv_div_sqrt_sq_sub_one_eq_zero
    (f f' : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (ha : f a = 1) (hb : f b = 1)
    (hinterior : ∀ x ∈ Ioo a b, 1 < f x)
    (hint : IntervalIntegrable
      (fun x => f' x / Real.sqrt ((f x)^2 - 1)) volume a b) :
    (∫ x in a..b, f' x / Real.sqrt ((f x)^2 - 1)) = 0 := by
  let F : ℝ → ℝ := fun x => Real.arcosh (f x)
  have hge (x : ℝ) (hx : x ∈ Icc a b) : 1 ≤ f x := by
    by_cases hxa : x = a
    · simpa [hxa] using ha.ge
    by_cases hxb : x = b
    · simpa [hxb] using hb.ge
    have hx' : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa),
      lt_of_le_of_ne hx.2 hxb⟩
    exact (hinterior x hx').le
  have hFcont : ContinuousOn F (Icc a b) :=
    Real.continuousOn_arcosh.comp hcont (fun x hx => hge x hx)
  have hFderiv (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt F (f' x / Real.sqrt ((f x)^2 - 1)) x := by
    have h := (Real.hasDerivAt_arcosh (hinterior x hx)).comp x (hderiv x hx)
    simpa only [F, Function.comp_def, div_eq_mul_inv, mul_comm] using h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hFcont hFderiv hint
  simpa only [F, ha, hb, Real.arcosh_zero, sub_self] using hi

end NLS.ComplexAnalysis
