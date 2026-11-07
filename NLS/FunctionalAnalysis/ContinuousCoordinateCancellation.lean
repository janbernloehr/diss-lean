import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-! A nonzero continuous linear coordinate can be cancelled from an
identity of continuous scalar functions even on its entire zero hyperplane. -/
noncomputable section
open Filter Topology
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_eq_zero_of_coordinate_mul (f : E → ℝ) (l : E →L[ℝ] ℝ) (e : E)
    (hle : l e=1) (hf : Continuous f) (he : ∀ z, l z*f z=0) : ∀ z, f z=0 := by
  intro z
  by_cases hz : l z=0
  · have hc : Continuous (fun t : ℝ => f (z+t • e)) := hf.comp (by fun_prop)
    have hnear : (fun t : ℝ => f (z+t • e)) =ᶠ[𝓝[≠] (0:ℝ)] (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htne : t≠0 := ht
      have hlt : l (z+t • e)=t := by simp [hz,hle]
      exact (mul_eq_zero.mp (he (z+t • e))).resolve_left (by simpa only [hlt] using htne)
    have hlim := tendsto_nhds_unique_of_eventuallyEq
      (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hnear
    simpa only [zero_smul,add_zero] using hlim
  · exact (mul_eq_zero.mp (he z)).resolve_left hz

end NLS.FunctionalAnalysis
