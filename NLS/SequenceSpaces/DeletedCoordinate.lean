import NLS.SequenceSpaces.Basic

/-!
# An `ℓᵖ` sequence with one coordinate omitted

The displacement parameter in the psi-function construction omits a
single integer index. We realize this Banach space as the closed kernel
of coordinate evaluation and construct its continuous projection from
the ambient integer-indexed `ℓᵖ` space.
-/

noncomputable section
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The closed `ℓᵖ` subspace with the `n`th coordinate deleted. -/
abbrev DeletedCoeff (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) : Type :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker

/-- The omitted-coordinate sequence space is complete. -/
instance (n : ℤ) : CompleteSpace (DeletedCoeff p n) := inferInstance

namespace Coeff

/-- Set the selected coordinate to zero, leaving every other
coefficient unchanged. -/
def deleteCoordinate (n : ℤ) : Coeff p →L[ℂ] Coeff p :=
  ContinuousLinearMap.id ℂ (Coeff p) -
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p n).comp
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n)

@[simp] theorem deleteCoordinate_apply_same (n : ℤ) (a : Coeff p) :
    deleteCoordinate n a n = 0 := by
  change a n - (lp.single p n (a n) : Coeff p) n = 0
  simp

theorem deleteCoordinate_apply_other (n m : ℤ) (hmn : m ≠ n) (a : Coeff p) :
    deleteCoordinate n a m = a m := by
  change a m - (lp.single p n (a n) : Coeff p) m = a m
  rw [lp.single_apply_ne _ _ _ hmn]
  simp

/-- The continuous projection lands in the omitted-coordinate space. -/
theorem deleteCoordinate_mem (n : ℤ) (a : Coeff p) :
    deleteCoordinate n a ∈ (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker := by
  change deleteCoordinate n a n = 0
  exact deleteCoordinate_apply_same n a

/-- The coordinate deletion is a genuine projection. -/
@[simp] theorem deleteCoordinate_idempotent (n : ℤ) (a : Coeff p) :
    deleteCoordinate n (deleteCoordinate n a) = deleteCoordinate n a := by
  ext m
  by_cases hmn : m = n
  · subst m
    simp
  · rw [deleteCoordinate_apply_other n m hmn]

/-- A sequence is fixed by deletion precisely when its selected
coordinate already vanishes. -/
theorem deleteCoordinate_eq_self_iff (n : ℤ) (a : Coeff p) :
    deleteCoordinate n a = a ↔ a n = 0 := by
  constructor
  · intro h
    have he := congrArg (fun x : Coeff p => x n) h
    simpa using he.symm
  · intro h
    ext m
    by_cases hmn : m = n
    · subst m
      simp [h]
    · exact deleteCoordinate_apply_other n m hmn a

/-- The projection, with codomain restricted to the closed Banach
subspace. -/
def deleteCoordinateTo (n : ℤ) : Coeff p →L[ℂ] DeletedCoeff p n :=
  (deleteCoordinate n).codRestrict _ (deleteCoordinate_mem n)

/-- Every omitted-coordinate sequence is reached by the projection. -/
theorem deleteCoordinateTo_surjective (n : ℤ) :
    Function.Surjective (deleteCoordinateTo (p := p) n) := by
  intro b
  refine ⟨b.1,?_⟩
  apply Subtype.ext
  exact (deleteCoordinate_eq_self_iff n b.1).2 b.2

end Coeff
end NLS
