import NLS.ZakharovShabat.SourcePsiFreeFrechet

/-!
# The invertible free psi Jacobian operator

The scalar Fréchet derivatives at the free data are the rows of
`2 · id` on the deleted-coordinate `ℓᵖ` space. This bounded operator
has inverse `(1/2) · id`. We do not yet identify it as the derivative
of a sequence-valued contour map; that requires a uniform `ℓᵖ` bound
for the contours.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The bounded operator whose coordinate rows are the free scalar
psi-equation derivatives. -/
def sourcePsiFreeJacobianOperator (n : ℤ) :
    DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
  (2 : ℂ) • ContinuousLinearMap.id ℂ (DeletedCoeff p n)

/-- Explicit bounded inverse of the free diagonal operator. -/
def sourcePsiFreeJacobianInverseOperator (n : ℤ) :
    DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
  (2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (DeletedCoeff p n)

theorem sourcePsiFreeJacobianOperator_apply (n : ℤ)
    (a : DeletedCoeff p n) :
    sourcePsiFreeJacobianOperator n a = (2 : ℂ) • a := rfl

theorem sourcePsiFreeJacobianInverseOperator_apply (n : ℤ)
    (a : DeletedCoeff p n) :
    sourcePsiFreeJacobianInverseOperator n a = (2 : ℂ)⁻¹ • a := rfl

/-- The inverse followed by the free operator is the identity. -/
theorem sourcePsiFreeJacobianInverse_left (n : ℤ)
    (a : DeletedCoeff p n) :
    sourcePsiFreeJacobianInverseOperator n
      (sourcePsiFreeJacobianOperator n a) = a := by
  rw [sourcePsiFreeJacobianOperator_apply,
    sourcePsiFreeJacobianInverseOperator_apply, smul_smul]
  norm_num

/-- The free operator followed by its inverse is the identity. -/
theorem sourcePsiFreeJacobianInverse_right (n : ℤ)
    (a : DeletedCoeff p n) :
    sourcePsiFreeJacobianOperator n
      (sourcePsiFreeJacobianInverseOperator n a) = a := by
  rw [sourcePsiFreeJacobianInverseOperator_apply,
    sourcePsiFreeJacobianOperator_apply, smul_smul]
  norm_num

/-- The free Jacobian is a continuous complex-linear equivalence of
the omitted-coordinate Banach space. -/
def sourcePsiFreeJacobianEquiv (n : ℤ) :
    DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n where
  toLinearEquiv := {
    toFun := sourcePsiFreeJacobianOperator n
    invFun := sourcePsiFreeJacobianInverseOperator n
    left_inv := sourcePsiFreeJacobianInverse_left n
    right_inv := sourcePsiFreeJacobianInverse_right n
    map_add' := (sourcePsiFreeJacobianOperator n).map_add
    map_smul' := (sourcePsiFreeJacobianOperator n).map_smul
  }
  continuous_toFun := (sourcePsiFreeJacobianOperator n).continuous
  continuous_invFun := (sourcePsiFreeJacobianInverseOperator n).continuous

/-- Each scalar derivative is precisely the corresponding coordinate
of the invertible free operator. -/
theorem fderiv_sourcePsiFreeEquation_eq_freeOperator_coordinate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (hmn : m ≠ n) (r : ℝ) (hr : 0 < r) (hrπ : r < Real.pi)
    (a : DeletedCoeff p n) :
    (fderiv ℂ (sourcePsiFreeEquation hp hp1 n m r)
      (0 : DeletedCoeff p n)) a =
      ((sourcePsiFreeJacobianOperator n a : DeletedCoeff p n) : Coeff p) m := by
  rw [fderiv_sourcePsiFreeEquation_apply hp hp1 n m hmn r hr hrπ,
    sourcePsiFreeJacobianOperator_apply]
  rfl

end NLS.ZakharovShabat
