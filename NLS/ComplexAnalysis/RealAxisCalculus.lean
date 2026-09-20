import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Real-axis calculus for complex differentiable functions

If a complex function is real on the real axis, its complex derivative
there is real too. Real Rolle's theorem then gives a zero of the full
complex derivative between equal real-axis values.
-/

open Set Complex
namespace NLS.ComplexAnalysis

/-- Complex derivatives on the real axis are real for functions preserving that axis. -/
theorem deriv_im_eq_zero_of_real_axis (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hr : ∀ x : ℝ, (f x).im = 0) (x : ℝ) : (deriv f x).im = 0 := by
  have he : (fun y : ℝ => ((f y).re : ℂ)) = fun y : ℝ => f y := by
    funext y
    apply Complex.ext <;> simp [hr y]
  have hd := (hf (x : ℂ)).hasDerivAt
  have hdR := hd.real_of_complex.ofReal_comp
  rw [he] at hdR
  have hh := hd.comp_ofReal.unique hdR
  simpa only [ofReal_im] using congrArg Complex.im hh

/-- Rolle's theorem on the real axis gives a zero of the complex derivative. -/
theorem exists_deriv_eq_zero_between_real (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hr : ∀ x : ℝ, (f x).im = 0) {a b : ℝ} (hab : a < b) (he : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f (c : ℂ) = 0 := by
  have hc : Continuous (fun x : ℝ => (f x).re) :=
    continuous_re.comp (hf.continuous.comp continuous_ofReal)
  obtain ⟨c,hc,hzero⟩ := exists_hasDerivAt_eq_zero hab hc.continuousOn (congrArg Complex.re he)
    (fun x _ => (hf (x : ℂ)).hasDerivAt.real_of_complex)
  refine ⟨c,hc,?_⟩
  apply Complex.ext
  · simpa only [zero_re] using hzero
  · simpa only [zero_im] using deriv_im_eq_zero_of_real_axis f hf hr c

end NLS.ComplexAnalysis
