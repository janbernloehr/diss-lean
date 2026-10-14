import NLS.ComplexAnalysis.CompactParameterBounds

/-!
# Uniform local bounds near a compact parameter slice

Local bounds for an arbitrary indexed family become one bound near a
compact slice. Continuity of the supremum over the indices is not needed.
-/

open Set
namespace NLS.ComplexAnalysis

theorem exists_uniform_bound_near_compact_slice
    {A B J : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (K : Set A) (hK : IsCompact K) (x : B) (f : A × B → J → ℝ)
    (hlocal : ∀ a ∈ K, ∃ U : Set (A × B), IsOpen U ∧ (a,x) ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ U, ∀ j, f q j ≤ C) :
    ∃ V : Set B, IsOpen V ∧ x ∈ V ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ V, ∀ a ∈ K, ∀ j, f (a,y) j ≤ C := by
  classical
  choose U ho hx C hC hb using fun a : K => hlocal a a.property
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover
    (fun a : K => (fun b : A => (b,x)) ⁻¹' U a)
    (fun a => (ho a).preimage (continuous_id.prodMk continuous_const)) (by
      intro a ha
      exact mem_iUnion.mpr ⟨⟨a,ha⟩,hx ⟨a,ha⟩⟩)
  let T : Set (A × B) := ⋃ a ∈ s, U a
  have hT : IsOpen T := isOpen_biUnion (fun a _ => ho a)
  have hslice : K ×ˢ ({x} : Set B) ⊆ T := by
    rintro ⟨a,y⟩ ⟨ha,hy⟩
    have hyx : y = x := mem_singleton_iff.mp hy
    subst y
    simpa only [T,mem_iUnion,mem_preimage] using hs ha
  obtain ⟨W,V,_,hV,hKW,hxV,hWV⟩ :=
    generalized_tube_lemma hK isCompact_singleton hT hslice
  refine ⟨V,hV,hxV (mem_singleton x),∑ a ∈ s, C a,
    Finset.sum_nonneg (fun a _ => hC a),?_⟩
  intro y hy a ha j
  have hmem : (a,y) ∈ T := hWV ⟨hKW ha,hy⟩
  obtain ⟨b,hbs,hq⟩ := mem_iUnion₂.mp hmem
  exact (hb b (a,y) hq j).trans (Finset.single_le_sum (fun b _ => hC b) hbs)

end NLS.ComplexAnalysis
