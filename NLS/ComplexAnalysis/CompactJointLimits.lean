import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! # Uniform limits from joint parameter limits on a compact set

Joint convergence of a family at every point of a compact parameter
set upgrades to uniform convergence when its limiting function is
continuous. This accommodates moving spectral evaluation points.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis

theorem tendstoUniformlyOn_of_joint_limits
    {A X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {l : Filter A} {F : A → X → Y} {f : X → Y} {K : Set X}
    (hK : IsCompact K) (hf : ContinuousOn f K)
    (hF : ∀ x ∈ K, Tendsto (fun q : A × X => F q.1 q.2)
      (l ×ˢ 𝓝[K] x) (𝓝 (f x))) : TendstoUniformlyOn F f l K := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro x hx
  have hlim := (hf x hx).tendsto.comp (tendsto_snd :
    Tendsto (fun q : A × X => q.2) (l ×ˢ 𝓝[K] x) (𝓝[K] x))
  exact (hlim.prodMk_nhds (hF x hx)).mono_right (nhds_le_uniformity (f x))

end NLS.ComplexAnalysis
