import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Topology.Order.Compact

/-! A compact continuous family of nonnegative decreasing tails has a
single vanishing envelope, attained by a family member at each cutoff. -/
noncomputable section
open Set Filter Topology
namespace NLS

/-- Compactness supplies an attained maximum envelope for a continuous
nonnegative tail family. Monotonicity upgrades pointwise decay to uniform decay. -/
theorem exists_vanishing_max_envelope_on_compact
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [Nonempty T]
    (f : ℕ → T → ℝ) (hc : ∀ N, Continuous (f N))
    (hn : ∀ N t, 0 ≤ f N t) (hm : ∀ t, Antitone (fun N => f N t))
    (hl : ∀ t, Tendsto (fun N => f N t) atTop (𝓝 0)) :
    ∃ V : ℕ → ℝ, (∀ N, 0 ≤ V N) ∧ (∀ N t, f N t ≤ V N) ∧
      (∀ N, ∃ t, V N = f N t) ∧ Tendsto V atTop (𝓝 0) := by
  have hex (N : ℕ) := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (univ : Set T).Nonempty) (hc N).continuousOn
  choose t ht hmax using hex
  let V := fun N => f N (t N)
  have hu : TendstoUniformlyOn f (fun _ => (0:ℝ)) atTop univ :=
    Antitone.tendstoUniformlyOn_of_forall_tendsto isCompact_univ
      (fun N => (hc N).continuousOn) (fun t _ => hm t)
      continuousOn_const (fun t _ => hl t)
  refine ⟨V,fun N => hn N (t N),fun N s => hmax N (mem_univ s),
    fun N => ⟨t N,rfl⟩,?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  exact ((Metric.tendstoUniformlyOn_iff.mp hu) ε hε).mono fun N hN => by
    simpa only [V,dist_comm] using hN (t N) (mem_univ _)

end NLS
