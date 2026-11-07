import NLS.FunctionalAnalysis.UniformCauchyLimit
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! Compactwise uniformly Cauchy families on locally compact domains.
Continuity is required only eventually, and the index filter is arbitrary. -/
noncomputable section
open Set Filter Topology
namespace NLS

/-- Uniform Cauchy control on a set is uniform Cauchy control of the
restricted functions on the entire subtype, including the empty set. -/
theorem uniformCauchyOn_iff_subtype
    {A T Y : Type*} [UniformSpace Y] (F : A → T → Y) (l : Filter A) (S : Set T) :
    UniformCauchySeqOn F l S ↔
      UniformCauchySeqOn (fun a (s : S) => F a s) l univ := by
  simp only [UniformCauchySeqOn, mem_univ, forall_const, Subtype.forall]

/-- Compactwise uniform Cauchy control gives one continuous limit on the
whole locally compact domain. The same limit works on every compact set. -/
theorem exists_continuous_limit_of_compactwise_uniformCauchy
    {A T Y : Type*} [TopologicalSpace T] [LocallyCompactSpace T]
    [UniformSpace Y] [CompleteSpace Y] {l : Filter A} [NeBot l]
    (F : A → T → Y) (hF : ∀ᶠ a in l, Continuous (F a))
    (hc : ∀ S : Set T, IsCompact S → UniformCauchySeqOn F l S) :
    ∃ g : C(T, Y), ∀ S : Set T, IsCompact S → TendstoUniformlyOn F g l S := by
  have hp (s : T) : ∃ y : Y, Tendsto (fun a => F a s) l (𝓝 y) :=
    cauchy_map_iff_exists_tendsto.mp
      ((hc {s} isCompact_singleton).cauchy_map (mem_singleton s))
  choose g hg using hp
  have hu (S : Set T) (hS : IsCompact S) : TendstoUniformlyOn F g l S :=
    (hc S hS).tendstoUniformlyOn_of_tendsto (fun s _ => hg s)
  have hgc : Continuous g :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mpr hu).continuous hF.frequently
  exact ⟨⟨g, hgc⟩, hu⟩

end NLS
