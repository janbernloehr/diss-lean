import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Normed.Module.Connected

/-! # Contractible neighborhoods in spaces with real normed charts

A chart pulls back a small convex ball in its target to a contractible
neighborhood in the original topology. This applies in particular to
every finite-dimensional topological manifold without boundary.
-/
noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis

/-- Real normed charts give a contractible neighborhood of every point. -/
theorem exists_contractible_neighborhood_of_chartedSpace
    (E X : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] (x : X) :
    ∃ V : Set X, V ∈ 𝓝 x ∧ ContractibleSpace V := by
  let e := chartAt E x
  have hy : e x ∈ e.target := mem_chart_target E x
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hy)
  let B := Metric.ball (e x) r
  let V := e.symm '' B
  have hV : V ∈ 𝓝 x := by
    have h := e.symm.image_mem_nhds hy (Metric.ball_mem_nhds (e x) hr)
    simpa only [OpenPartialHomeomorph.left_inv e (mem_chart_source E x)] using h
  let h : B ≃ₜ V := e.symm.homeomorphOfImageSubsetSource hsub rfl
  let : ContractibleSpace B := Metric.contractibleSpace_ball hr
  exact ⟨V,hV,h.symm.contractibleSpace⟩

end NLS.FunctionalAnalysis
