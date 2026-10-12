import NLS.FunctionalAnalysis.ProjectionRank
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Ranges under continuous linear conjugation

Conjugation preserves the dimension of a range and of its intersection with
a transported subspace. These are linear equivalences; no isometry of the
ambient norms is assumed.
-/
noncomputable section
namespace NLS.ConjugatedRanges
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Range membership under conjugation. -/
theorem mem_range (e : E ≃L[ℂ] F) (A : F →L[ℂ] F) (x : E) :
    x ∈ (e.symm.conjContinuousAlgEquiv A).range ↔ e x ∈ A.range := by
  constructor
  · rintro ⟨y,hy⟩
    refine ⟨e y,?_⟩
    change A (e y) = e x
    rw [← hy]
    exact (e.apply_symm_apply _).symm
  · rintro ⟨y,hy⟩
    refine ⟨e.symm y,?_⟩
    change e.symm (A (e (e.symm y))) = x
    change A y = e x at hy
    rw [e.apply_symm_apply,hy,e.symm_apply_apply]

/-- Conjugated operators have linearly equivalent ranges. -/
def rangeEquiv (e : E ≃L[ℂ] F) (A : F →L[ℂ] F) :
    (e.symm.conjContinuousAlgEquiv A).range ≃ₗ[ℂ] A.range where
  toFun x := ⟨e x.val,(mem_range e A x.val).mp x.property⟩
  invFun x := ⟨e.symm x.val,(mem_range e A (e.symm x.val)).mpr (by rw [e.apply_symm_apply]; exact x.property)⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact e.map_add x.val y.val
  map_smul' c x := by apply Subtype.ext; exact e.map_smul c x.val

/-- The range intersections with corresponding subspaces are linearly equivalent. -/
def rangeInfEquiv (e : E ≃L[ℂ] F) (A : F →L[ℂ] F) (S : Submodule ℂ F) :
    ↥((e.symm.conjContinuousAlgEquiv A).range ⊓ S.comap e.toLinearMap) ≃ₗ[ℂ] ↥(A.range ⊓ S) where
  toFun x := ⟨e x.val,(mem_range e A x.val).mp x.property.1,x.property.2⟩
  invFun x := ⟨e.symm x.val,
    (mem_range e A (e.symm x.val)).mpr (by rw [e.apply_symm_apply]; exact x.property.1),
    by change e (e.symm x.val) ∈ S; rw [e.apply_symm_apply]; exact x.property.2⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact e.map_add x.val y.val
  map_smul' c x := by apply Subtype.ext; exact e.map_smul c x.val

end NLS.ConjugatedRanges
