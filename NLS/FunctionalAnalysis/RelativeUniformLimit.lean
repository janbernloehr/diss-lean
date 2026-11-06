import Mathlib.Topology.UniformSpace.Cauchy

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Classical

namespace NLS.FunctionalAnalysis



/-- A uniformly continuous map into a complete space has an actual relative
limit at every point in the closure of its domain. -/
theorem exists_tendsto_nhdsWithin_of_uniformContinuousOn
    {α β : Type*} [UniformSpace α] [UniformSpace β] [CompleteSpace β]
    (f : α → β) (s : Set α) (hf : UniformContinuousOn f s) (a : α) (ha : a∈closure s) :
    ∃ b : β, Tendsto f (𝓝[s] a) (𝓝 b) := by
  let : NeBot (𝓝[s] a) := mem_closure_iff_nhdsWithin_neBot.mp ha
  have hc : Cauchy (𝓝[s] a) := cauchy_nhds.mono nhdsWithin_le_nhds
  have hm : Cauchy (Filter.map f (𝓝[s] a)) := hc.map_of_le hf inf_le_right
  exact cauchy_iff_exists_le_nhds.mp hm

end NLS.FunctionalAnalysis
