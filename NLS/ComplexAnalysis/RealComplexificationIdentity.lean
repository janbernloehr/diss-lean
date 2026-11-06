import NLS.ComplexAnalysis.AppendixELocalTaylor

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.ComplexAnalysis

variable {R E F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A nonempty real slice determines an analytic function on its connected
open complex domain, for an actual topological real complexification. -/
theorem RealComplexification.eqOn_zero_of_nonempty_real_slice
    (c : RealComplexification R E) (U : Set E) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hreal : (U ∩ c.realLocus).Nonempty)
    (f : E → F) (hf : AnalyticOnNhd ℂ f U)
    (hzero : EqOn f 0 (U ∩ c.realLocus)) : EqOn f 0 U := by
  obtain ⟨u,hu⟩ := hreal
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hu.1
    (sourceLemmaE2_zero_germ c U hU hu f hf hzero)

end NLS.ComplexAnalysis
