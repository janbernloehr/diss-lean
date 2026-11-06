import NLS.ComplexAnalysis.AnalyticCollapsedQuadraticSolution

/-! # The normalized value of a regular quadratic-root primitive at collapse -/
noncomputable section
set_option autoImplicit false
open Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem quadratic_solution_value_at_collapse (H f : ℂ → ℂ)
    (hH : AnalyticAt ℂ H 0) (hf : DifferentiableAt ℂ f 0)
    (he : (fun z : ℂ => z^2*deriv H z+z*H z) =ᶠ[𝓝 0] (fun z => f z-f 0)) :
    H 0=deriv f 0 := by
  have hd : HasDerivAt (fun z : ℂ => z^2*deriv H z+z*H z) (H 0) 0 := by
    simpa using!
      (((hasDerivAt_id (0 : ℂ)).pow 2).mul hH.deriv.differentiableAt.hasDerivAt).add
        ((hasDerivAt_id (0 : ℂ)).mul hH.differentiableAt.hasDerivAt)
  exact (hd.congr_of_eventuallyEq he.symm).unique (hf.hasDerivAt.sub_const (f 0))

end NLS.ComplexAnalysis
