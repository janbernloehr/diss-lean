import NLS.ComplexAnalysis.RealAxisCalculus
import NLS.ComplexAnalysis.StrictDerivativeTest

/-!
# Second derivatives and strict extrema on the real axis

Complex differentiability identifies the first two real derivatives of
the real-part restriction. If a function preserves the real axis, a
nondegenerate complex critical point on that axis is a strict real extremum.
-/

open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

/-- The derivative of the real-part restriction is the real part of the complex derivative. -/
theorem deriv_real_axis_re (f : ℂ → ℂ) (hf : Differentiable ℂ f) (x : ℝ) :
    deriv (fun y : ℝ => (f y).re) x = (deriv f x).re :=
  (hf (x : ℂ)).hasDerivAt.real_of_complex.deriv

/-- The second real derivative agrees with the real part of the second complex derivative. -/
theorem second_deriv_real_axis_re (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hdf : Differentiable ℂ (deriv f)) (x : ℝ) :
    deriv (deriv (fun y : ℝ => (f y).re)) x = (deriv (deriv f) x).re := by
  have he : deriv (fun y : ℝ => (f y).re) = fun y : ℝ => (deriv f y).re :=
    funext (deriv_real_axis_re f hf)
  rw [he]
  exact deriv_real_axis_re (deriv f) hdf x

/-- A twice complex differentiable real-axis-preserving function has real second derivatives there. -/
theorem second_deriv_im_eq_zero_of_real_axis (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hdf : Differentiable ℂ (deriv f)) (hr : ∀ x : ℝ, (f x).im = 0) (x : ℝ) :
    (deriv (deriv f) x).im = 0 :=
  deriv_im_eq_zero_of_real_axis (deriv f) hdf (deriv_im_eq_zero_of_real_axis f hf hr) x

/-- A nondegenerate complex critical point on a preserved real axis is a strict real local extremum. -/
theorem strict_local_extremum_of_complex_critical (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hdf : Differentiable ℂ (deriv f)) (hr : ∀ x : ℝ, (f x).im = 0) (x : ℝ)
    (hzero : deriv f (x : ℂ) = 0) (hne : deriv (deriv f) (x : ℂ) ≠ 0) :
    (∀ᶠ y : ℝ in 𝓝[≠] x, (f x).re < (f y).re) ∨
      (∀ᶠ y : ℝ in 𝓝[≠] x, (f y).re < (f x).re) := by
  apply strict_local_extremum_of_second_derivative_ne_zero (f := fun y : ℝ => (f y).re)
    (continuous_re.comp (hf.continuous.comp continuous_ofReal))
  · rw [deriv_real_axis_re f hf x,hzero,zero_re]
  · rw [second_deriv_real_axis_re f hf hdf x]
    intro he
    apply hne
    exact Complex.ext he (second_deriv_im_eq_zero_of_real_axis f hf hdf hr x)

end NLS.ComplexAnalysis
