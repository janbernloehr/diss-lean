import Mathlib.Analysis.Complex.RealDeriv

/-!
# Reality of a complex derivative from local real-axis values

Only values in a neighborhood of the differentiation point are needed
to conclude that the complex derivative preserves the real axis.
-/

open Complex Filter
open scoped Topology
namespace NLS.ComplexAnalysis

/-- If a complex-differentiable function takes real values on the
nearby real axis, its complex derivative at the real basepoint is real. -/
theorem HasDerivAt.im_eq_zero_of_eventually_real
    (f : ℂ → ℂ) (f' : ℂ) (x : ℝ)
    (hf : HasDerivAt f f' (x:ℂ))
    (hr : ∀ᶠ y : ℝ in 𝓝 x, (f (y:ℂ)).im = 0) :
    f'.im = 0 := by
  have hdR := hf.real_of_complex
  have hdC := hdR.ofReal_comp
  have he : (fun y : ℝ => (((f (y:ℂ)).re : ℝ) : ℂ)) =ᶠ[𝓝 x]
      (fun y : ℝ => f (y:ℂ)) := by
    filter_upwards [hr] with y hy
    apply Complex.ext <;> simp [hy]
  have hh := (hf.comp_ofReal).unique (hdC.congr_of_eventuallyEq he.symm)
  simpa only [Complex.ofReal_im] using congrArg Complex.im hh

end NLS.ComplexAnalysis
