import Mathlib.Topology.IsLocalHomeomorph

/-! A continuous lifted curve agrees with a local inverse branch as long
as its image remains in that branch domain and its initial point agrees.
No global covering or properness assumption is used. -/
noncomputable section
open Set
namespace NLS.Topology

/-- Unique continuous lifting in a specified local inverse chart. -/
theorem eqOn_localInverse_lift {X Y A : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [TopologicalSpace A] (f : X → Y) (hf : IsLocalHomeomorph f)
    (e : OpenPartialHomeomorph Y X) (he : (e.symm : X → Y)=f)
    (S : Set A) (hS : IsPreconnected S) (γ : A → X) (hγ : ContinuousOn γ S)
    (hmem : ∀ t ∈ S, f (γ t) ∈ e.source) (a : A) (ha : a ∈ S)
    (hzero : e (f (γ a))=γ a) : EqOn (fun t => e (f (γ t))) γ S := by
  have hc : ContinuousOn (fun t => e (f (γ t))) S :=
    e.continuousOn.comp (hf.continuous.continuousOn.comp hγ (fun _ _ => mem_univ _)) hmem
  have hcomp : EqOn (f ∘ (fun t => e (f (γ t)))) (f ∘ γ) S := by
    intro t ht
    change f (e (f (γ t)))=f (γ t)
    have h := e.left_inv (hmem t ht)
    change e.symm (e (f (γ t)))=f (γ t) at h
    rw [he] at h
    exact h
  exact (T2Space.isSeparatedMap f).eqOn_of_comp_eqOn hf.isLocallyInjective hS hc hγ hcomp ha hzero

end NLS.Topology
