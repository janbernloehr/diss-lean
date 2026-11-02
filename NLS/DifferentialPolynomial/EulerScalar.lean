import NLS.DifferentialPolynomial.EulerLagrange

/-! # Scalar multiplication in the Euler operator -/
noncomputable section
open MvPolynomial
namespace NLS.DifferentialPolynomial

theorem iterate_spatialDerivative_C_mul (c : ℂ) (p : Polynomial) (n : ℕ) :
    ((spatialDerivative : Polynomial → Polynomial)^[n]) (C c*p) =
      C c*((spatialDerivative : Polynomial → Polynomial)^[n]) p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp [Derivation.leibniz, smul_eq_mul]

theorem eulerDerivative_C_mul (field : Bool) (c : ℂ) (p : Polynomial) :
    eulerDerivative field (C c*p) = C c*eulerDerivative field p := by
  classical
  by_cases hc : c = 0
  · subst c; simp [eulerDerivative]
  have hd (v : Jet) : pderiv v (C c*p) = C c*pderiv v p := by
    simp [Derivation.leibniz, smul_eq_mul]
  simp only [eulerDerivative, MvPolynomial.vars_C_mul c hc, hd,
    iterate_spatialDerivative_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> ring

end NLS.DifferentialPolynomial
