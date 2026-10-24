import NLS.FunctionalAnalysis.CubeFixedPoint

/-! # Face-compatible labels for covers of the finite unit cube

Label a cover member by the least upper face it meets, or by the cube
 dimension if it meets none. A set avoiding opposite faces cannot carry
 the label of any lower face it meets.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.CubicalSperner
variable {n m : ℕ}

/-- The upper faces touched by one set in the finite cube. -/
def cubeUpperFaces (C : Set (@unit_cube n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun k => ∃ x ∈ C, x.val k = 1)

/-- Least touched upper face, with the final label reserved for no upper face. -/
def cubeCoverLabel (C : Set (@unit_cube n)) : ℕ :=
  if h : (cubeUpperFaces C).Nonempty then ((cubeUpperFaces C).min' h).val else n

/-- No member of this cover meets both faces in any coordinate direction. -/
def CubeCoverAvoidsOppositeFaces (C : Fin m → Set (@unit_cube n)) : Prop :=
  ∀ i k, ¬ ((∃ x ∈ C i, x.val k = 0) ∧ (∃ x ∈ C i, x.val k = 1))

theorem cubeCoverLabel_le (C : Set (@unit_cube n)) : cubeCoverLabel C ≤ n := by
  classical
  unfold cubeCoverLabel
  split
  · exact (Fin.is_lt _).le
  · exact le_rfl

theorem cubeCoverLabel_le_of_upper {C : Set (@unit_cube n)} (k : Fin n)
    (h : ∃ x ∈ C, x.val k = 1) : cubeCoverLabel C ≤ k.val := by
  classical
  have hk : k ∈ cubeUpperFaces C := by simpa [cubeUpperFaces] using h
  have hn : (cubeUpperFaces C).Nonempty := ⟨k,hk⟩
  simp only [cubeCoverLabel,dif_pos hn]
  exact Finset.min'_le _ _ hk

theorem exists_upper_of_cubeCoverLabel_eq {C : Set (@unit_cube n)} (k : Fin n)
    (h : cubeCoverLabel C = k.val) : ∃ x ∈ C, x.val k = 1 := by
  classical
  by_cases hn : (cubeUpperFaces C).Nonempty
  · have he : (cubeUpperFaces C).min' hn = k := by
      apply Fin.ext
      simpa only [cubeCoverLabel,dif_pos hn] using h
    have hk := Finset.min'_mem (cubeUpperFaces C) hn
    rw [he] at hk
    simpa [cubeUpperFaces] using hk
  · simp only [cubeCoverLabel,dif_neg hn] at h
    exact False.elim (Nat.ne_of_gt k.is_lt h)

theorem cubeCoverLabel_face_rules (C : Fin m → Set (@unit_cube n))
    (hC : CubeCoverAvoidsOppositeFaces C) (i : Fin m) (x : @unit_cube n) (hx : x ∈ C i) :
    cubeCoverLabel (C i) ≤ n ∧ ∀ k : Fin n,
      (x.val k = 0 → cubeCoverLabel (C i) ≠ k.val) ∧
      (x.val k = 1 → cubeCoverLabel (C i) ≤ k.val) := by
  refine ⟨cubeCoverLabel_le _,fun k => ⟨?_,?_⟩⟩
  · intro h0 he
    exact hC i k ⟨⟨x,hx,h0⟩,exists_upper_of_cubeCoverLabel_eq k he⟩
  · intro h1
    exact cubeCoverLabel_le_of_upper k ⟨x,hx,h1⟩

end NLS.CubicalSperner
