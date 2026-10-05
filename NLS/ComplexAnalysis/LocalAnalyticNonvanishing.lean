import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology

/-! # Density from local analytic scalar criteria

A nonempty open set locally detected by nonvanishing analytic functions is
dense in a connected open domain. The local functions need not agree.
-/
noncomputable section
open Set Filter Topology Metric
namespace NLS.ComplexAnalysis
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The identity theorem propagates density across overlapping local
analytic nonvanishing criteria, without requiring a global determinant. -/
theorem subset_closure_of_local_analytic_nonvanishing
    {U S : Set X} (hU : IsOpen U) (hconn : IsPreconnected U) (hS : IsOpen S)
    (hne : (U ∩ S).Nonempty)
    (hlocal : ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ d : X → ℂ,
      AnalyticOnNhd ℂ d V ∧ ∀ y ∈ V ∩ U, y ∈ S ↔ d y ≠ 0) : U ⊆ closure S := by
  have hstart : (U ∩ interior (closure S)).Nonempty := by
    obtain ⟨x,hx,hxs⟩ := hne
    exact ⟨x,hx,(interior_mono subset_closure) (by rwa [hS.interior_eq])⟩
  have hprop : closure (interior (closure S)) ∩ U ⊆ interior (closure S) := by
    rintro x ⟨hxc,hxU⟩
    have hxS : x ∈ closure S := by
      simpa only [closure_closure] using (closure_mono interior_subset hxc)
    obtain ⟨V,hV,hxV,d,hd,hcrit⟩ := hlocal x hxU
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ((hV.inter hU).mem_nhds ⟨hxV,hxU⟩)
    obtain ⟨w,hwB,hwS⟩ := mem_closure_iff_nhds.mp hxS (ball x r) (ball_mem_nhds x hr)
    have hwne : d w ≠ 0 := (hcrit w (hball hwB)).mp hwS
    have hdB : AnalyticOnNhd ℂ d (ball x r) := hd.mono (fun y hy => (hball hy).1)
    have hBclosure : ball x r ⊆ closure S := by
      intro y hy
      by_contra hyS
      have hz : d =ᶠ[𝓝 y] 0 := by
        filter_upwards [isOpen_ball.mem_nhds hy,isClosed_closure.isOpen_compl.mem_nhds hyS] with z hzB hzS
        change d z = 0
        by_contra hdz
        exact hzS (subset_closure ((hcrit z (hball hzB)).mpr hdz))
      have hall := hdB.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball x r).isPreconnected hy hz
      exact hwne (hall hwB)
    exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (ball_mem_nhds x hr) hBclosure)
  exact (hconn.subset_of_closure_inter_subset isOpen_interior hstart hprop).trans interior_subset

end NLS.ComplexAnalysis
