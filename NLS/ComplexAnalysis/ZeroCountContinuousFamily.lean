import NLS.ComplexAnalysis.ZeroCountHomotopy
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Analytic zero counts in a continuous family

Compactness of the contour makes boundary nonvanishing locally uniform
in any topological parameter. Rouché then proves local constancy, and
connectedness identifies the counts at the endpoints of a homotopy.
-/

noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis

/-- Boundary nonvanishing at one parameter makes the analytic count
stable in a neighborhood of that parameter. -/
theorem eventually_analyticZeroCount_eq_of_continuous_family
    {T : Type*} [TopologicalSpace T] (F : T → ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hF : ContinuousOn F.uncurry (univ ×ˢ sphere c r))
    (ha : ∀ t, AnalyticOnNhd ℂ (F t) (closedBall c r))
    (t : T) (hz : ∀ z ∈ sphere c r, F t z ≠ 0) :
    ∀ᶠ s in 𝓝 t, analyticZeroCount (F s) (closedBall c r) =
      analyticZeroCount (F t) (closedBall c r) := by
  obtain ⟨δ,hδ,hbound⟩ := (isCompact_sphere c r).exists_forall_le'
    (((ha t).continuousOn.mono sphere_subset_closedBall).norm)
    (fun z hz' => norm_pos_iff.mpr (hz z hz'))
  obtain ⟨V,hV,hclose⟩ := (isCompact_sphere c r).mem_uniformity_of_prod
    hF (mem_univ t) (Metric.dist_mem_uniformity hδ)
  rw [nhdsWithin_univ] at hV
  filter_upwards [hV] with s hs
  apply analyticZeroCount_eq_of_boundary_lt hr (ha t) (ha s)
  intro z hzc
  have hd := hclose s hs z hzc
  change dist (F s z) (F t z) < δ at hd
  exact (show ‖F s z-F t z‖ < δ by rwa [dist_eq_norm] at hd).trans_le (hbound z hzc)


end NLS.ComplexAnalysis
