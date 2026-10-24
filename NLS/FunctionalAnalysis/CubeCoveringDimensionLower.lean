import NLS.FunctionalAnalysis.CubeLebesgueCovering
import NLS.FunctionalAnalysis.CoveringDimensionBasic
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.UnitInterval

/-! # The cube covering-dimension lower bound

An explicit finite open cover avoids opposite faces. Any open refinement
can be shrunk to a closed cover, so Lebesgue's covering lemma forces
multiplicity at least one more than the dimension of the cube.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped unitInterval
open NLS.CubicalSperner
namespace NLS.FunctionalAnalysis

/-- A finite open cover of the cube whose members avoid opposite faces. -/
theorem exists_cube_open_cover_avoiding_faces (n : ℕ) :
    ∃ U : FiniteOpenCover (@unit_cube n), CubeCoverAvoidsOppositeFaces U.sets := by
  classical
  let e := Fintype.equivFin (Fin n → Bool)
  let V : (Fin n → Bool) → Set (@unit_cube n) := fun b =>
    {x | ∀ k, if b k then x.val k < (2/3 : ℝ) else (1/3 : ℝ) < x.val k}
  have ho (b) : IsOpen (V b) := by
    rw [show V b = ⋂ k, {x : @unit_cube n | if b k then x.val k < (2/3 : ℝ)
      else (1/3 : ℝ) < x.val k} by ext x; simp only [V,mem_ofPred_eq,mem_iInter]]
    apply isOpen_iInter_of_finite
    intro k
    cases hb : b k
    · exact isOpen_lt continuous_const ((continuous_apply k).comp continuous_subtype_val)
    · exact isOpen_lt ((continuous_apply k).comp continuous_subtype_val) continuous_const
  have hc (x : @unit_cube n) : ∃ b, x ∈ V b := by
    let b : Fin n → Bool := fun k => decide (x.val k < (2/3 : ℝ))
    refine ⟨b,fun k => ?_⟩
    change (if decide (x.val k < (2/3 : ℝ)) then _ else _)
    by_cases h : x.val k < (2/3 : ℝ)
    · simp [h]
    · simp only [h,decide_false,Bool.false_eq_true,if_false]
      linarith
  let U : FiniteOpenCover (@unit_cube n) := {
    count := Fintype.card (Fin n → Bool)
    sets i := V (e.symm i)
    isOpen i := ho _
    covers x := by
      obtain ⟨b,hb⟩ := hc x
      exact ⟨e b,by simpa using hb⟩ }
  refine ⟨U,?_⟩
  intro i k h
  obtain ⟨⟨x,hx,h0⟩,⟨y,hy,h1⟩⟩ := h
  have hxk := hx k
  have hyk := hy k
  cases hb : e.symm i k
  · simp only [hb,Bool.false_eq_true,if_false,h0] at hxk
    norm_num at hxk
  · simp only [hb,if_true,h1] at hyk
    norm_num at hyk

/-- The (n+1)-cube does not have covering dimension at most n. -/
theorem not_hasCoveringDimensionLE_unit_cube (n : ℕ) :
    ¬ HasCoveringDimensionLE (@unit_cube (n+1)) n := by
  classical
  intro h
  obtain ⟨U,hU⟩ := exists_cube_open_cover_avoiding_faces (n+1)
  obtain ⟨V,hVU,hV⟩ := h U
  have hcover : ⋃ i, V.sets i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i,hi⟩ := V.covers x
    exact Set.mem_iUnion.mpr ⟨i,hi⟩
  obtain ⟨C,hCcover,hCclosed,hCV⟩ := exists_iUnion_eq_closed_subset V.isOpen
    (fun _ => Set.toFinite _) hcover
  have hCfaces : CubeCoverAvoidsOppositeFaces C := by
    intro i k hfaces
    obtain ⟨j,hj⟩ := hVU i
    apply hU j k
    obtain ⟨⟨x,hx,h0⟩,⟨y,hy,h1⟩⟩ := hfaces
    exact ⟨⟨x,hj (hCV i hx),h0⟩,⟨y,hj (hCV i hy),h1⟩⟩
  have hC (x) : ∃ i, x ∈ C i := by
    apply Set.mem_iUnion.mp
    rw [hCcover]
    exact Set.mem_univ _
  obtain ⟨x,hx⟩ := cube_lebesgue_covering C hCclosed hC hCfaces
  have hm : (Finset.univ.filter (fun i => x ∈ C i)).card ≤ V.multiplicity x := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hCV i (Finset.mem_filter.mp hi).2⟩
  have := hV x
  omega

/-- The coordinatewise interval cube and the interval in the real function space agree. -/
def unitCubeHomeomorphIntervalPi (n : ℕ) : @unit_cube n ≃ₜ (Fin n → unitInterval) where
  toFun x k := ⟨x.val k,⟨x.property.1 k,x.property.2 k⟩⟩
  invFun x := ⟨fun k => (x k).val,⟨fun k => (x k).property.1,fun k => (x k).property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi (fun k =>
    ((continuous_apply k).comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (continuous_pi (fun k =>
    continuous_subtype_val.comp (continuous_apply k))).subtype_mk _

/-- The numerical lower bound in the product-of-unit-intervals representation. -/
theorem not_hasCoveringDimensionLE_cube (n : ℕ) :
    ¬ HasCoveringDimensionLE (Fin (n+1) → unitInterval) n := by
  intro h
  exact not_hasCoveringDimensionLE_unit_cube n (h.homeomorph (unitCubeHomeomorphIntervalPi (n+1)).symm)

end NLS.FunctionalAnalysis
