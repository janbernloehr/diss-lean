import NLS.FunctionalAnalysis.CoveringDimensionBasic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Connected spaces cannot have covering dimension zero

A finite cover of multiplicity at most one consists of pairwise disjoint
clopen sets. On a preconnected space its nonempty members cover the whole
space. A two-member proper open cover of a nontrivial T1 space therefore
obstructs covering dimension zero.
-/
noncomputable section
open Set
namespace NLS.FunctionalAnalysis
universe u
variable {X : Type u} [TopologicalSpace X]

/-- Multiplicity at most one makes distinct finite-cover members disjoint. -/
theorem FiniteOpenCover.disjoint_of_multiplicity_le_one
    (U : FiniteOpenCover X) (hU : ∀ x, U.multiplicity x ≤ 1)
    (i j : Fin U.count) (hij : i ≠ j) : Disjoint (U.sets i) (U.sets j) := by
  classical
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hsub : ({i,j} : Finset (Fin U.count)) ⊆
      Finset.univ.filter (fun k => x ∈ U.sets k) := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxj⟩
  have hb := (Finset.card_le_card hsub).trans (hU x)
  have hcard : ({i,j} : Finset (Fin U.count)).card = 2 := by simp [hij]
  rw [hcard] at hb
  omega

/-- Every member of a multiplicity-one finite open cover is clopen. -/
theorem FiniteOpenCover.isClopen_of_multiplicity_le_one
    (U : FiniteOpenCover X) (hU : ∀ x, U.multiplicity x ≤ 1)
    (i : Fin U.count) : IsClopen (U.sets i) := by
  have he : (U.sets i)ᶜ = ⋃ j : Fin U.count, ⋃ _ : j ≠ i, U.sets j := by
    ext x
    constructor
    · intro hx
      obtain ⟨j,hj⟩ := U.covers x
      have hji : j ≠ i := by rintro rfl; exact hx hj
      exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hji,hj⟩⟩
    · intro hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      obtain ⟨hji,hj⟩ := mem_iUnion.mp hj
      intro hi
      exact Set.disjoint_left.mp (U.disjoint_of_multiplicity_le_one hU j i hji) hj hi
  refine ⟨isOpen_compl_iff.mp ?_,U.isOpen i⟩
  rw [he]
  exact isOpen_iUnion fun j => isOpen_iUnion fun _ => U.isOpen j

/-- A nontrivial preconnected T1 space does not have covering dimension zero. -/
theorem not_hasCoveringDimensionLE_zero_of_preconnected
    [T1Space X] [PreconnectedSpace X] [Nontrivial X] :
    ¬ HasCoveringDimensionLE X 0 := by
  classical
  obtain ⟨a,b,hab⟩ := exists_pair_ne X
  let U : FiniteOpenCover X := {
    count := 2
    sets := ![{a}ᶜ,{b}ᶜ]
    isOpen := by intro i; fin_cases i <;> exact isClosed_singleton.isOpen_compl
    covers := by
      intro x
      by_cases hx : x = a
      · refine ⟨1,?_⟩
        change x ≠ b
        exact hx ▸ hab
      · exact ⟨0,hx⟩ }
  intro h
  obtain ⟨V,hVU,hV⟩ := h U
  obtain ⟨j,hj⟩ := V.covers a
  have he : V.sets j = univ := (V.isClopen_of_multiplicity_le_one hV j).eq_univ ⟨a,hj⟩
  obtain ⟨i,hi⟩ := hVU j
  have hall (x : X) : x ∈ U.sets i := hi (he.symm ▸ mem_univ x)
  fin_cases i
  · exact hall a rfl
  · exact hall b rfl

end NLS.FunctionalAnalysis
