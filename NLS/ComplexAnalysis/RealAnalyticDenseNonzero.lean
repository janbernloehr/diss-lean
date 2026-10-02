import NLS.ComplexAnalysis.ConvexRealAnalyticIdentity

/-! # Dense nonzero sets for real analytic functions on Banach spaces

A real analytic function on the whole space that has a nonzero value
cannot vanish on any open ball. The convex real identity principle
therefore makes its nonzero locus dense.
-/

noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A nontrivial globally real analytic function has a dense nonzero locus. -/
theorem dense_ne_zero_of_real_analytic
    (f : E → F) (hf : AnalyticOnNhd ℝ f univ) (a : E) (ha : f a ≠ 0) :
    Dense {x | f x ≠ 0} := by
  apply Metric.dense_iff.mpr
  intro x ε hε
  by_contra h
  have hzero : ∀ y ∈ ball x ε, f y = 0 := by
    intro y hy
    by_contra hn
    exact h ⟨y,hy,hn⟩
  have heq : f =ᶠ[𝓝 x] (fun _ => 0) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hε)) hzero
  have hglobal := AnalyticOnNhd.eqOn_of_convex_of_eventuallyEq f (fun _ => 0) univ
    isOpen_univ (convex_univ : Convex ℝ (univ : Set E)) hf analyticOnNhd_const x (mem_univ _) heq
  exact ha (hglobal (mem_univ a))

end NLS.ComplexAnalysis
