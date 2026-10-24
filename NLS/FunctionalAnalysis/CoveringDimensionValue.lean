import NLS.FunctionalAnalysis.CoveringDimensionBasic
import Mathlib.Data.ENat.Lattice

/-! # The numerical covering-dimension invariant

The value is bottom (the conventional dimension -1) for an empty space,
the least finite open-refinement bound when one exists, and infinity
otherwise. Its finite bounds are exactly `HasCoveringDimensionLE`.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.FunctionalAnalysis
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

private theorem not_top_le_natCast (n : ℕ) : ¬ (⊤ : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
  intro h
  have he : (n : ℕ∞) = ⊤ := WithBot.coe_injective (top_le_iff.mp h)
  exact ENat.natCast_ne_top n he

/-- Standard covering dimension, with bottom representing -1 and top infinity. -/
def coveringDimension (X : Type u) [TopologicalSpace X] : WithBot ℕ∞ := by
  classical
  exact if IsEmpty X then ⊥ else
    if h : ∃ n : ℕ, HasCoveringDimensionLE X n then (Nat.find h : WithBot ℕ∞) else ⊤

/-- Finite numerical bounds agree with the finite-open-refinement definition. -/
theorem coveringDimension_le_iff (n : ℕ) :
    coveringDimension X ≤ (n : WithBot ℕ∞) ↔ HasCoveringDimensionLE X n := by
  classical
  by_cases he : IsEmpty X
  · let := he
    simp only [coveringDimension,if_pos he,bot_le,true_iff]
    exact hasCoveringDimensionLE_of_isEmpty n
  · by_cases h : ∃ k, HasCoveringDimensionLE X k
    · simp only [coveringDimension,if_neg he,dif_pos h]
      constructor
      · intro hn
        have hkn : Nat.find h ≤ n := by exact_mod_cast hn
        exact (Nat.find_spec h).mono hkn
      · intro hn
        have hkn := Nat.find_min' h hn
        exact_mod_cast hkn
    · simp only [coveringDimension,if_neg he,dif_neg h]
      constructor
      · intro hn
        exact False.elim (not_top_le_natCast n hn)
      · intro hn
        exact False.elim (h ⟨n,hn⟩)

/-- Exactly the empty spaces have dimension bottom. -/
theorem coveringDimension_eq_bot_iff : coveringDimension X = ⊥ ↔ IsEmpty X := by
  classical
  by_cases he : IsEmpty X
  · simp [coveringDimension,he]
  · simp only [coveringDimension,if_neg he]
    split <;> simp [he]

/-- Infinite covering dimension means that no natural number is a dimension bound. -/
theorem coveringDimension_eq_top_iff :
    coveringDimension X = ⊤ ↔ ∀ n : ℕ, ¬ HasCoveringDimensionLE X n := by
  constructor
  · intro h n hn
    have hb := (coveringDimension_le_iff n).mpr hn
    rw [h] at hb
    exact not_top_le_natCast n hb
  · intro h
    apply ENat.WithBot.eq_top_iff_forall_ge.mpr
    intro n
    exact (lt_of_not_ge (fun hn => h n ((coveringDimension_le_iff n).mp hn))).le

/-- A homeomorphism preserves the numerical covering dimension, including empty spaces. -/
theorem coveringDimension_homeomorph (e : X ≃ₜ Y) :
    coveringDimension X = coveringDimension Y := by
  classical
  have he : IsEmpty X ↔ IsEmpty Y := by
    constructor
    · intro h
      exact ⟨fun y => h.false (e.symm y)⟩
    · intro h
      exact ⟨fun x => h.false (e x)⟩
  by_cases hx : IsEmpty X
  · rw [coveringDimension_eq_bot_iff.mpr hx,coveringDimension_eq_bot_iff.mpr (he.mp hx)]
  · have hy : ¬ IsEmpty Y := fun h => hx (he.mpr h)
    by_cases hX : ∃ n, HasCoveringDimensionLE X n
    · have hY : ∃ n, HasCoveringDimensionLE Y n :=
        ⟨Nat.find hX,(Nat.find_spec hX).homeomorph e⟩
      have hfind : Nat.find hX = Nat.find hY := by
        apply Nat.le_antisymm
        · exact Nat.find_min' hX ((Nat.find_spec hY).homeomorph e.symm)
        · exact Nat.find_min' hY ((Nat.find_spec hX).homeomorph e)
      simp only [coveringDimension,if_neg hx,if_neg hy,dif_pos hX,dif_pos hY,hfind]
    · have hY : ¬ ∃ n, HasCoveringDimensionLE Y n := by
        rintro ⟨n,hn⟩
        exact hX ⟨n,hn.homeomorph e.symm⟩
      simp only [coveringDimension,if_neg hx,if_neg hy,dif_neg hX,dif_neg hY]

/-- Nonempty spaces have nonnegative covering dimension. -/
theorem zero_le_coveringDimension [Nonempty X] : (0 : WithBot ℕ∞) ≤ coveringDimension X := by
  classical
  have he : ¬ IsEmpty X := not_isEmpty_of_nonempty X
  unfold coveringDimension
  simp only [if_neg he]
  split
  · exact_mod_cast Nat.zero_le _
  · exact le_top

/-- A space with at most one point has covering dimension at most zero. -/
theorem hasCoveringDimensionLE_zero_of_subsingleton [Subsingleton X] :
    HasCoveringDimensionLE X 0 := by
  classical
  cases isEmpty_or_nonempty X with
  | inl he =>
    let := he
    exact hasCoveringDimensionLE_of_isEmpty 0
  | inr hn =>
    let := hn
    intro U
    let x0 : X := Classical.choice hn
    obtain ⟨i,hi⟩ := U.covers x0
    let V : FiniteOpenCover X := {
      count := 1
      sets _ := U.sets i
      isOpen _ := U.isOpen i
      covers x := ⟨0,by simpa only [Subsingleton.elim x x0] using hi⟩ }
    refine ⟨V,fun _ => ⟨i,Set.Subset.rfl⟩,?_⟩
    intro x
    change (Finset.univ.filter (fun j : Fin 1 => x ∈ V.sets j)).card ≤ 0+1
    exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- A one-point space has numerical covering dimension zero. -/
theorem coveringDimension_eq_zero_of_subsingleton [Nonempty X] [Subsingleton X] :
    coveringDimension X = 0 :=
  le_antisymm ((coveringDimension_le_iff 0).mpr hasCoveringDimensionLE_zero_of_subsingleton)
    zero_le_coveringDimension

end NLS.FunctionalAnalysis
