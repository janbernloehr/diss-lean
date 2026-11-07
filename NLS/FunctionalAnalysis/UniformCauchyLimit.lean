import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Cauchy

/-! Uniformly Cauchy families in complete spaces, with arbitrary index filters
and arbitrary testing sets. No topology on the testing parameter is needed. -/
noncomputable section
open Set Filter Topology
namespace NLS

/-- A uniformly Cauchy family with a nontrivial convergence filter has a
uniform limit on any testing set, including an empty set. -/
theorem exists_limit_of_uniformCauchyOn
    {A B Y : Type*} [UniformSpace Y] [CompleteSpace Y] [Nonempty Y]
    {l : Filter A} [NeBot l] (F : A → B → Y) (S : Set B)
    (hF : UniformCauchySeqOn F l S) :
    ∃ g : B → Y, TendstoUniformlyOn F g l S := by
  classical
  have he : ∀ b : B, ∃ y : Y, b ∈ S → Tendsto (fun a => F a b) l (𝓝 y) := by
    intro b
    by_cases hb : b ∈ S
    · obtain ⟨y, hy⟩ := cauchy_map_iff_exists_tendsto.mp (hF.cauchy_map hb)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨Classical.choice inferInstance, fun h => False.elim (hb h)⟩
  choose g hg using he
  exact ⟨g, hF.tendstoUniformlyOn_of_tendsto hg⟩

end NLS
