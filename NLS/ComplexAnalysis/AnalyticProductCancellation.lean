import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic

/-! # Cancellation of a nonzero continuous factor in an analytic identity -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PreconnectedSpace E]

theorem eq_zero_of_analytic_mul_eq_zero (f g : E → ℂ)
    (hg : AnalyticOnNhd ℝ g univ) (hfg : ∀ x, f x*g x = 0)
    (b : E) (hf : ContinuousAt f b) (hb : f b ≠ 0) : ∀ x, g x = 0 := by
  have hnear : g =ᶠ[𝓝 b] fun _ => 0 := by
    filter_upwards [hf.eventually_ne hb] with x hx
    exact (mul_eq_zero.mp (hfg x)).resolve_left hx
  have he := hg.eq_of_eventuallyEq analyticOnNhd_const hnear
  exact fun x => congrFun he x

end NLS.ComplexAnalysis
