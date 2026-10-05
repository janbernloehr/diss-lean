import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Complex.Basic

/-! # Schur complements of bounded block operators

Eliminating an invertible lower-right block reduces bijectivity to the
Schur complement on the first factor, as in Appendix I of the dissertation.
-/
noncomputable section
namespace NLS.SchurComplement
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A bounded operator in two-by-two block form. -/
def block (A : E →L[ℂ] E) (B : F →L[ℂ] E) (C : E →L[ℂ] F) (D : F →L[ℂ] F) :
    E × F →L[ℂ] E × F := (A.coprod B).prod (C.coprod D)

@[simp] theorem block_apply (A : E →L[ℂ] E) (B : F →L[ℂ] E)
    (C : E →L[ℂ] F) (D : F →L[ℂ] F) (x : E × F) :
    block A B C D x = (A x.1 + B x.2, C x.1 + D x.2) := rfl

/-- The Schur complement after eliminating the second coordinate. -/
def schur (A : E →L[ℂ] E) (B : F →L[ℂ] E) (C : E →L[ℂ] F) (D : F ≃L[ℂ] F) :
    E →L[ℂ] E := A - B.comp (D.symm.toContinuousLinearMap.comp C)

@[simp] theorem schur_apply (A : E →L[ℂ] E) (B : F →L[ℂ] E)
    (C : E →L[ℂ] F) (D : F ≃L[ℂ] F) (x : E) :
    schur A B C D x = A x - B (D.symm (C x)) := rfl

/-- Schur elimination preserves and reflects bijectivity, including at
singular finite-dimensional blocks. -/
theorem bijective_block_iff (A : E →L[ℂ] E) (B : F →L[ℂ] E)
    (C : E →L[ℂ] F) (D : F ≃L[ℂ] F) :
    Function.Bijective (block A B C D.toContinuousLinearMap) ↔
      Function.Bijective (schur A B C D) := by
  constructor
  · rintro ⟨hi,hs⟩
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro x hx
      have he : block A B C D.toContinuousLinearMap (x,-D.symm (C x)) = 0 := by
        apply Prod.ext
        · simpa [sub_eq_add_neg] using hx
        · simp
      exact congrArg Prod.fst (hi (he.trans (map_zero _).symm))
    · intro x
      obtain ⟨⟨u,v⟩,huv⟩ := hs (x,0)
      have hv : v = -D.symm (C u) := by
        have h := congrArg Prod.snd huv
        change C u + D v = 0 at h
        have h' := congrArg D.symm (eq_neg_of_add_eq_zero_right h)
        simpa using h'
      refine ⟨u,?_⟩
      have h := congrArg Prod.fst huv
      simpa [hv,sub_eq_add_neg] using h
  · rintro ⟨hi,hs⟩
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      rintro ⟨u,v⟩ huv
      have hv : v = -D.symm (C u) := by
        have h := congrArg Prod.snd huv
        change C u + D v = 0 at h
        have h' := congrArg D.symm (eq_neg_of_add_eq_zero_right h)
        simpa using h'
      have hu : schur A B C D u = 0 := by
        have h := congrArg Prod.fst huv
        simpa [hv,sub_eq_add_neg] using h
      have hu0 : u = 0 := hi (hu.trans (map_zero _).symm)
      simp [hu0] at hv
      exact Prod.ext hu0 hv
    · rintro ⟨x,y⟩
      obtain ⟨u,hu⟩ := hs (x - B (D.symm y))
      refine ⟨(u,D.symm (y-C u)),?_⟩
      apply Prod.ext
      · change A u + B (D.symm (y-C u)) = x
        simp only [map_sub] at *
        rw [schur_apply] at hu
        calc
          A u + (B (D.symm y) - B (D.symm (C u))) =
              (A u - B (D.symm (C u))) + B (D.symm y) := by abel
          _ = x := by rw [hu]; abel
      · change C u + D (D.symm (y-C u)) = y
        simp

end NLS.SchurComplement
