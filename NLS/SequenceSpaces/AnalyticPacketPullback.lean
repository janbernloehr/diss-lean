import Mathlib.Analysis.Analytic.Linear
import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.Analytic.Composition

/-! Pull back a genuinely bounded analytic coordinate packet in abstract
Banach spaces, preserving one common domain and all coordinate identities. -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS

theorem mem_of_subset_preimage {E F : Type*} (J : E → F) (U : Set E) (V : Set F)
    (h : U⊆J ⁻¹' V) (a : E) (ha : a∈U) : J a∈V := h ha

theorem exists_analytic_packet_pullback
    {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Q : X → E) (U : Set X) (hU : IsOpen U) (hQ : AnalyticOnNhd ℂ Q U)
    (V : Set E) (hV : IsOpen V) (g : E → F) (hg : AnalyticOnNhd ℂ g V)
    (K : ℝ) (hn : ∀ a∈V, ‖g a‖≤K) (coord : F → ℤ → ℂ) (c : ℕ+ → E → ℂ)
    (hz : ∀ a∈V, ∀ j : ℤ, j≤0 → coord (g a) j=0)
    (hp : ∀ a∈V, ∀ n : ℕ+, coord (g a) (n : ℤ)=c n a)
    (x0 : X) (hx : x0∈U) (hxV : Q x0∈V) :
    ∃ T : Set X, IsOpen T ∧ x0∈T ∧ T⊆U ∧ (∀ x∈T, Q x∈V) ∧
      ∃ f : X → F, AnalyticOnNhd ℂ f T ∧ (∀ x∈T, ‖f x‖≤K) ∧
        (∀ x∈T, ∀ j : ℤ, j≤0 → coord (f x) j=0) ∧
        ∀ x∈T, ∀ n : ℕ+, coord (f x) (n : ℤ)=c n (Q x) := by
  let T := U∩Q ⁻¹' V
  refine ⟨T,hQ.continuousOn.isOpen_inter_preimage hU hV,⟨hx,hxV⟩,
    (fun _ h => h.1),(fun _ h => h.2),(fun x => g (Q x)),?_,
    (fun _ h => hn _ h.2),(fun _ h => hz _ h.2),(fun _ h => hp _ h.2)⟩
  intro x hxT
  exact (hg _ hxT.2).comp (hQ x hxT.1)

/-- Transport a coherent target map to a stronger cone through an actual
bounded linear inclusion, retaining the original raw coordinates. -/
theorem exists_analytic_cone_pullback
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (J : E →L[ℂ] F) (C : Set E) (D V : Set F)
    (coord : G → ℤ → ℂ) (ω : F → ℤ → ℂ) (f : F → G)
    (hC : ∀ a∈C, J a∈D) (hV : IsOpen V) (hD : D⊆V)
    (hf : AnalyticOnNhd ℂ f V)
    (hz : ∀ a∈V, ∀ j : ℤ, j≤0 → coord (f a) j=0)
    (hr : ∀ a∈D, ∀ j : ℤ, coord (f a) j=ω a j) :
    ∃ U : Set E, ∃ g : E → G, IsOpen U ∧ C⊆U ∧ AnalyticOnNhd ℂ g U ∧
      (∀ a∈U, ∀ j : ℤ, j≤0 → coord (g a) j=0) ∧
      ∀ a∈C, ∀ j : ℤ, coord (g a) j=ω (J a) j := by
  refine ⟨J ⁻¹' V,(fun a => f (J a)),hV.preimage J.continuous,
    (fun a ha => hD (hC a ha)),?_,(fun a ha => hz _ ha),(fun a ha => hr _ (hC a ha))⟩
  intro a ha
  exact (hf _ ha).comp (J.analyticAt a)

end NLS
