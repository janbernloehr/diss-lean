import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Connected.Clopen

/-! # Uniqueness along a smooth autonomous trajectory

Local uniqueness from local Lipschitz continuity propagates over any
preconnected open time domain. Only smoothness near the reference
trajectory is needed; no global Lipschitz bound is assumed.
-/
noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two solutions agreeing once agree on a preconnected open time domain
when the vector field is `C¹` along the reference solution. -/
theorem eqOn_of_autonomous_hasDerivAt {v : E → E} {f g : ℝ → E} {U : Set ℝ}
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hv : ∀ t ∈ U, ContDiffAt ℝ 1 v (f t))
    (hf : ∀ t ∈ U, HasDerivAt f (v (f t)) t)
    (hg : ∀ t ∈ U, HasDerivAt g (v (g t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ U) (heq : f t₀ = g t₀) : EqOn f g U := by
  have : PreconnectedSpace U := Subtype.preconnectedSpace hc
  have hfc : Continuous (fun t : U => f t.val) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hf t.val t.property).continuousAt.comp continuous_subtype_val.continuousAt
  have hgc : Continuous (fun t : U => g t.val) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hg t.val t.property).continuousAt.comp continuous_subtype_val.continuousAt
  have hclosed : IsClosed {t : U | f t.val = g t.val} := isClosed_eq hfc hgc
  have hopen : IsOpen {t : U | f t.val = g t.val} := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨K,S,hS,hLip⟩ := (hv t.val t.property).exists_lipschitzOnWith
    have hfm : ∀ᶠ r in 𝓝 t.val, f r ∈ S := (hf t.val t.property).continuousAt.tendsto.eventually hS
    have hgm : ∀ᶠ r in 𝓝 t.val, g r ∈ S := by
      have hs : S ∈ 𝓝 (g t.val) := ht ▸ hS
      exact (hg t.val t.property).continuousAt.tendsto.eventually hs
    have he : f =ᶠ[𝓝 t.val] g := ODE_solution_unique_of_eventually
      (v := fun _ => v) (s := fun _ => S)
      (Eventually.of_forall fun _ => hLip)
      (by filter_upwards [hU.mem_nhds t.property,hfm] with r hr hfr; exact ⟨hf r hr,hfr⟩)
      (by filter_upwards [hU.mem_nhds t.property,hgm] with r hr hgr; exact ⟨hg r hr,hgr⟩) ht
    exact continuous_subtype_val.continuousAt.tendsto.eventually he
  have hall := (show IsClopen {t : U | f t.val = g t.val} from ⟨hclosed,hopen⟩).eq_univ
    ⟨⟨t₀,ht₀⟩,heq⟩
  intro t ht
  have hm : (⟨t,ht⟩ : U) ∈ {r : U | f r.val = g r.val} := by rw [hall]; trivial
  exact hm

end NLS.FunctionalAnalysis
