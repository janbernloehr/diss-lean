import NLS.ComplexAnalysis.CompactSliceLocalBounds

/-! Local joint properties along a compact slice hold uniformly on
one neighborhood of the parameter. This includes simultaneous equality
of arbitrarily indexed analytic families, with no extra bound premise. -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis

theorem exists_uniform_local_property_near_compact_slice
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (K : Set A) (hK : IsCompact K) (x : B) (P : A × B → Prop)
    (hlocal : ∀ a ∈ K, ∃ U : Set (A × B), IsOpen U ∧ (a,x) ∈ U ∧ ∀ q ∈ U, P q) :
    ∃ V : Set B, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, ∀ a ∈ K, P (a,y) := by
  obtain ⟨V,hV,hx,_,_,hP⟩ := exists_uniform_property_near_compact_slice K hK x (fun q _ => P q)
    (fun _ _ _ _ h => h) (by
      intro a ha
      obtain ⟨U,hU,hx,hP⟩ := hlocal a ha
      exact ⟨U,hU,hx,0,le_rfl,fun q hq => hP q hq⟩)
  exact ⟨V,hV,hx,hP⟩

end NLS.ComplexAnalysis
