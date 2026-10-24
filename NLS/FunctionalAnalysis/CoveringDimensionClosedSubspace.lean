import NLS.FunctionalAnalysis.CoveringDimensionBasic
import Mathlib.Data.Fin.VecNotation

/-! # Covering dimension of closed subspaces

A finite open cover of a closed subspace extends to the ambient space by
adding the complement. Restricting a bounded-multiplicity refinement gives
the required refinement on the closed subspace. This monotonicity is the
bridge from finite cubes inside a product to its covering dimension.
-/
noncomputable section
open Set
namespace NLS.FunctionalAnalysis
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A closed subspace inherits every finite covering-dimension upper bound. -/
theorem HasCoveringDimensionLE.closed_subspace {n : ℕ}
    (hX : HasCoveringDimensionLE X n) (A : Set X) (hA : IsClosed A) :
    HasCoveringDimensionLE A n := by
  classical
  by_cases hne : Nonempty A
  · obtain ⟨x₀⟩ := hne
    intro U
    obtain ⟨i₀,_⟩ := U.covers x₀
    choose W hW heq using fun i => isOpen_induced_iff.mp (U.isOpen i)
    let E : FiniteOpenCover X := {
      count := U.count+1
      sets := Fin.cases Aᶜ W
      isOpen := Fin.cases hA.isOpen_compl hW
      covers := by
        intro x
        by_cases hx : x ∈ A
        · obtain ⟨i,hi⟩ := U.covers ⟨x,hx⟩
          refine ⟨i.succ,?_⟩
          have h : (⟨x,hx⟩ : A) ∈ Subtype.val ⁻¹' W i := by
            rw [heq i]
            exact hi
          exact h
        · exact ⟨0,hx⟩ }
    obtain ⟨V,hVE,horder⟩ := hX E
    refine ⟨V.comap Subtype.val continuous_subtype_val,?_,fun x => horder x.val⟩
    intro j
    obtain ⟨i,hi⟩ := hVE j
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k,rfl⟩
    · refine ⟨i₀,fun x hx => ?_⟩
      have hnot : x.val ∉ A := hi hx
      exact (hnot x.property).elim
    · refine ⟨k,fun x hx => ?_⟩
      rw [← heq k]
      exact hi hx
  · let : IsEmpty A := not_nonempty_iff.mp hne
    exact hasCoveringDimensionLE_of_isEmpty n

/-- A closed embedding transfers every ambient covering-dimension upper bound. -/
theorem HasCoveringDimensionLE.of_isClosedEmbedding {n : ℕ}
    (hY : HasCoveringDimensionLE Y n) {f : X → Y} (hf : Topology.IsClosedEmbedding f) :
    HasCoveringDimensionLE X n := by
  have h := hY.closed_subspace (range f) hf.isClosed_range
  exact h.homeomorph hf.isEmbedding.toHomeomorph.symm

end NLS.FunctionalAnalysis
