import NLS.DifferentialPolynomial.EulerLagrange

/-! # Euler derivatives on an explicit finite jet set

Adding unused jets to the finite Euler sum does not change it. This
allows physical low-order density calibrations without a support assumption.
-/
noncomputable section
set_option autoImplicit false
open MvPolynomial
namespace NLS.DifferentialPolynomial

/-- Iterating the spatial derivation preserves the zero polynomial. -/
theorem iterate_spatialDerivative_zero (n : ℕ) :
    ((spatialDerivative : Polynomial → Polynomial)^[n]) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,map_zero]

/-- The actual Euler sum can be evaluated on ANY finite jet set containing
all variables of the density; every extra summand vanishes. -/
theorem eulerDerivative_eq_sum_of_vars_subset (field : Bool) (p : Polynomial) (S : Finset Jet)
    (hS : p.vars ⊆ S) :
    eulerDerivative field p = ∑ v ∈ S, if v.1 = field then
      C ((-1 : ℂ)^v.2)*((spatialDerivative : Polynomial → Polynomial)^[v.2]) (pderiv v p) else 0 := by
  classical
  apply Finset.sum_subset hS
  intro v _ hv
  rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hv,iterate_spatialDerivative_zero]
  split_ifs <;> simp only [mul_zero]

end NLS.DifferentialPolynomial
