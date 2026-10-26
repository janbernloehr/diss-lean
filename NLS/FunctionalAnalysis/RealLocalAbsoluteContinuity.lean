import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Global absolute continuity from local bounds off a null exceptional set -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
namespace NLS.FunctionalAnalysis

/-- Local absolute continuity on intervals around every point outside a
measure-null exceptional set implies absolute continuity on the whole line. -/
theorem absolutelyContinuous_of_local_Icc_off_null (μ ν : Measure ℝ) (E : Set ℝ)
    (hE : μ E = 0)
    (hloc : ∀ x ∉ E, ∃ δ : ℝ, 0 < δ ∧ μ.restrict (Icc (x-δ) (x+δ)) ≪ ν) :
    μ ≪ ν := by
  intro s hs
  rw [← measure_sdiff_null hE]
  apply measure_null_of_locally_null
  intro x hx
  obtain ⟨δ,hδ,hac⟩ := hloc x hx.2
  refine ⟨(s \ E) ∩ Icc (x-δ) (x+δ), ?_, ?_⟩
  · exact inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)))
  · apply measure_mono_null (inter_subset_inter_left _ sdiff_subset)
    simpa only [Measure.restrict_apply' measurableSet_Icc] using hac hs

end NLS.FunctionalAnalysis
