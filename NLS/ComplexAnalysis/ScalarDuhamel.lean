import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Scalar variation of constants on a real interval

The integrating factor gives the free-propagator integral formula without
any smallness assumption on the coefficient or the continuous forcing.
-/

noncomputable section
open Set Complex intervalIntegral
namespace NLS.ComplexAnalysis

theorem hasDerivAt_complex_exp_mul (c : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (c * s)) (exp (c * t) * c) t := by
  simpa using (Complex.ofRealCLM.hasDerivAt.const_mul c).cexp

theorem exp_mul_propagator (c : ℂ) (t s : ℝ) :
    exp (c * t) * exp (-c * s) = exp (c * (t - s)) := by
  rw [← exp_add]
  congr 1
  ring

/-- The scalar Duhamel formula, with only interior derivatives required. -/
theorem scalar_duhamel (c : ℂ) (u f : ℝ → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hu : Continuous u) (hf : Continuous f)
    (hd : ∀ s ∈ Ioo 0 t, HasDerivAt u (c * u s + f s) s) :
    u t = exp (c * t) * u 0 + ∫ s in 0..t, exp (c * (t - s)) * f s := by
  have hder : ∀ s ∈ Ioo 0 t,
      HasDerivAt (fun s : ℝ => exp (-c * s) * u s) (exp (-c * s) * f s) s := by
    intro s hs
    convert! (hasDerivAt_complex_exp_mul (-c) s).mul (hd s hs) using 1
    ring
  have hc : Continuous (fun s : ℝ => exp (-c * s) * u s) := by fun_prop
  have hcf : Continuous (fun s : ℝ => exp (-c * s) * f s) := by fun_prop
  have hi := integral_eq_sub_of_hasDerivAt_of_le ht hc.continuousOn hder
    (hcf.intervalIntegrable 0 t)
  have he : exp (c * t) * exp (-c * t) = 1 := by
    rw [exp_mul_propagator]
    simp
  have hi' := congrArg (fun w : ℂ => exp (c * t) * w) hi
  rw [← intervalIntegral.integral_const_mul] at hi'
  have hk : (fun s : ℝ => exp (c * t) * (exp (-c * s) * f s)) =
      (fun s : ℝ => exp (c * (t - s)) * f s) := by
    funext s
    rw [← mul_assoc, exp_mul_propagator]
  rw [hk] at hi'
  simp only [Complex.ofReal_zero, mul_zero, exp_zero, one_mul, mul_sub,
    ← mul_assoc, he] at hi'
  simp only [mul_sub]
  linear_combination -hi'

end NLS.ComplexAnalysis
