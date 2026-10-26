import NLS.ZakharovShabat.L2FloquetPeriodicMatrix

/-! # Cancellation of the periodic Floquet factors in the physical mode kernel -/
noncomputable section
set_option autoImplicit false
open Matrix Module Complex
namespace NLS.ZakharovShabat

/-- Each periodic column is the original fundamental mode times its compensating exponential. -/
theorem l2FloquetPeriodicMatrix_col (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) (t : ℝ) (j : Fin 2) :
    (l2FloquetPeriodicMatrix u z b μ t).col j =
      Complex.exp (-(t : ℂ)*Complex.log (μ j)) • (l2WholeLineFundamentalMatrix u z t *ᵥ b j) := rfl

/-- The inverse fundamental matrix removes exactly the physical factor of the periodic basis. -/
theorem l2WholeLineFundamental_inv_mul_periodic (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) (s : ℝ) :
    (l2WholeLineFundamentalMatrix u z s)⁻¹ * l2FloquetPeriodicMatrix u z b μ s =
      (Pi.basisFun ℂ (Fin 2)).toMatrix b *
        diagonal (fun j => Complex.exp (-(s : ℂ)*Complex.log (μ j))) := by
  rw [l2FloquetPeriodicMatrix_eq_mul_diagonal,← Matrix.mul_assoc,← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_l2WholeLineFundamentalMatrix u z s)),Matrix.one_mul]

/-- A diagonal one-sided exponential kernel becomes the original projected
fundamental kernel after the periodic change of basis. -/
theorem l2FloquetPeriodicMatrix_modeKernel (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ)
    (i : Fin 2) (P : Matrix (Fin 2) (Fin 2) ℂ)
    (hP : ∀ j, P *ᵥ b j = if j = i then b j else 0) (t s : ℝ) :
    l2FloquetPeriodicMatrix u z b μ t *
      diagonal (Pi.single i (Complex.exp (Complex.log (μ i)*((t-s : ℝ) : ℂ)))) *
        (l2FloquetPeriodicMatrix u z b μ s)⁻¹ =
      l2WholeLineFundamentalMatrix u z t * P * (l2WholeLineFundamentalMatrix u z s)⁻¹ := by
  apply (isUnit_l2FloquetPeriodicMatrix u z b μ s).mul_right_cancel
  rw [Matrix.mul_assoc _ _ (l2FloquetPeriodicMatrix u z b μ s),
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_l2FloquetPeriodicMatrix u z b μ s)),Matrix.mul_one,
    Matrix.mul_assoc _ _ (l2FloquetPeriodicMatrix u z b μ s),
    l2WholeLineFundamental_inv_mul_periodic]
  apply Matrix.ext_of_mulVec_single
  intro j
  simp only [← Matrix.mulVec_mulVec]
  simp only [Matrix.diagonal_mulVec_single,mul_one]
  simp only [Matrix.mulVec_single,op_smul_eq_smul]
  have hcol : ((Pi.basisFun ℂ (Fin 2)).toMatrix b).col j = b j := by
    ext k
    simp [Matrix.col,Module.Basis.toMatrix_apply]
  simp only [l2FloquetPeriodicMatrix_col,hcol,Matrix.mulVec_smul,hP]
  by_cases hj : j = i
  · subst j
    simp only [Pi.single_eq_same,ite_true,smul_smul]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp [hj]

end NLS.ZakharovShabat
