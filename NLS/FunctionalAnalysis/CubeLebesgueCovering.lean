import NLS.FunctionalAnalysis.CubeCoverLabel
import NLS.FunctionalAnalysis.CubeClosedLabels

/-! # Lebesgue's covering lemma for the finite cube

A finite closed cover of the n-cube, none of whose members meets opposite
faces, has a point belonging to at least n+1 distinct members.
-/
noncomputable section
set_option autoImplicit false
open Set Classical
namespace NLS.CubicalSperner
variable {n m : ℕ}

theorem cube_lebesgue_covering (C : Fin m → Set (@unit_cube n))
    (hclosed : ∀ i, IsClosed (C i)) (hcover : ∀ x, ∃ i, x ∈ C i)
    (hfaces : CubeCoverAvoidsOppositeFaces C) :
    ∃ x, n+1 ≤ (Finset.univ.filter (fun i => x ∈ C i)).card := by
  classical
  let D : Fin (n+1) → Set (@unit_cube n) := fun c =>
    ⋃ i : {i : Fin m // cubeCoverLabel (C i) = c.val}, C i.val
  have hDclosed (c) : IsClosed (D c) := isClosed_iUnion_of_finite (fun i => hclosed i.val)
  have hDcover (x) : ∃ c, x ∈ D c := by
    obtain ⟨i,hi⟩ := hcover x
    let c : Fin (n+1) := ⟨cubeCoverLabel (C i),Nat.lt_succ_of_le (cubeCoverLabel_le _)⟩
    refine ⟨c,Set.mem_iUnion.mpr ?_⟩
    exact ⟨⟨i,rfl⟩,hi⟩
  have hDface : ∀ c x, x ∈ D c → ∀ k : Fin n,
      (x.val k = 0 → c.val ≠ k.val) ∧ (x.val k = 1 → c.val ≤ k.val) := by
    intro c x hx k
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    simpa only [i.property] using (cubeCoverLabel_face_rules C hfaces i.val x hi).2 k
  obtain ⟨x,hx⟩ := exists_mem_all_cube_closed_labels D hDclosed hDcover hDface
  have hs (c : Fin (n+1)) : ∃ i : Fin m, cubeCoverLabel (C i) = c.val ∧ x ∈ C i := by
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hx c)
    exact ⟨i.val,i.property,hi⟩
  choose sel hlabel hmem using hs
  have hinj : Function.Injective sel := by
    intro c d h
    apply Fin.ext
    rw [← hlabel c,← hlabel d,h]
  have hsub : Finset.univ.image sel ⊆ Finset.univ.filter (fun i => x ∈ C i) := by
    intro i hi
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmem c⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin] at hcard
  exact ⟨x,hcard⟩

end NLS.CubicalSperner
