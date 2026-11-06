import NLS.SequenceSpaces.DeletedCoordinate

/-! # Literal restriction of a bounded equivalence to omitted-coordinate charts -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1≤p)]

/-- An actual bounded equivalence preserving the zero-coordinate kernel
restricts to the SAME closed omitted-coordinate chart in both directions. -/
def deletedRestrictionEquiv (n : ℤ) (Q : Coeff p ≃L[ℂ] Coeff p)
    (hQ : ∀ a : Coeff p, Q a n=0 ↔ a n=0) : DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n where
  toLinearEquiv := {
    toFun := (Q.toContinuousLinearMap.comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).codRestrict _
      (fun a => (hQ a.val).mpr a.property)
    invFun := (Q.symm.toContinuousLinearMap.comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).codRestrict _
      (fun a => (hQ (Q.symm a.val)).mp (by rw [Q.apply_symm_apply];exact a.property))
    left_inv := by intro a;apply Subtype.ext;exact Q.symm_apply_apply a.val
    right_inv := by intro a;apply Subtype.ext;exact Q.apply_symm_apply a.val
    map_add' := by intro a b;apply Subtype.ext;exact Q.map_add a.val b.val
    map_smul' := by intro c a;apply Subtype.ext;exact Q.map_smul c a.val }
  continuous_toFun := ((Q.toContinuousLinearMap.comp
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).codRestrict _ _).continuous
  continuous_invFun := ((Q.symm.toContinuousLinearMap.comp
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).codRestrict _ _).continuous

@[simp] theorem deletedRestrictionEquiv_apply (n : ℤ) (Q : Coeff p ≃L[ℂ] Coeff p)
    (hQ : ∀ a : Coeff p, Q a n=0 ↔ a n=0) (a : DeletedCoeff p n) :
    (deletedRestrictionEquiv n Q hQ a).val=Q a.val := rfl

end NLS.Coeff
