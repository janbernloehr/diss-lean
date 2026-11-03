import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # A local two-point Lipschitz estimate for an analytic scalar chart -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem exists_local_lipschitz_bound_of_analyticAt (f : ℂ → ℂ) (a : ℂ)
    (hf : AnalyticAt ℂ f a) :
    ∃ L delta : ℝ, 0 < L ∧ 0 < delta ∧
      ∀ x ∈ ball a delta, ∀ y ∈ ball a delta, ‖f x-f y‖ ≤ L*‖x-y‖ := by
  obtain ⟨K,U,hU,hLip⟩ := hf.contDiffAt.exists_lipschitzOnWith
  obtain ⟨delta,hdelta,hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨(K : ℝ)+1,delta,by positivity,hdelta,?_⟩
  intro x hx y hy
  have hh := hLip.dist_le_mul x (hball hx) y (hball hy)
  simp only [dist_eq_norm] at hh
  nlinarith [norm_nonneg (x-y)]

end NLS.ComplexAnalysis
