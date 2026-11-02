import NLS.MKdV.HierarchyRestriction

/-! # Checked first interfaces for arXiv:1601.07580v1

These declarations expose the exact current domains. They do not assert the
full vector-field, frequency, or Birkhoff-coordinate theorems of the article.
-/
noncomputable section
open Complex NLS.ZakharovShabat NLS.MKdV
namespace NLS.Articles.MKdVNLSHierarchies

/-- The vanishing clause of Theorem 1 (p. 3), on H^(2m-1).
For m=1 this is exactly the stated H¹ endpoint. -/
theorem theorem1_even_vanishing_original_domain
    (m : ℕ) (hm : 1 ≤ m) (u : ScalarSobolev (2*m-1)) :
    diagonalNLSHamiltonian (2*m-1) (2*m) (by omega) u = 0 :=
  diagonalNLSHamiltonian_even_eq_zero (2*m-1) m hm (by omega) u

/-- The swap part of Theorem 2(i) (p. 3) as a Fréchet-covector identity
at the printed H^(k-1) regularity. L²-gradient identification is separate. -/
theorem theorem2_i_swap_covectors (k : ℕ) (hk : 1 ≤ k)
    (ab : SobolevSource (k-1)) :
    (fderiv ℂ (fun cd => sobolevNLSHamiltonian (k-1) cd k (by omega))
      (hierarchyComponentSwap (k-1) ab)).comp (hierarchyComponentSwap (k-1)) =
      (-1 : ℂ)^(k-1) •
        fderiv ℂ (fun cd => sobolevNLSHamiltonian (k-1) cd k (by omega)) ab := by
  simpa only [Nat.sub_add_cancel hk] using
    fderiv_sobolevNLSHamiltonian_swap (k-1) (k-1) (by omega) ab

/-- The source's R_α acting on the original complex Sobolev pair. -/
def phaseRotation (s : ℕ) (α : ℝ) : SobolevSource s →L[ℂ] SobolevSource s :=
  hierarchyReciprocalScaling s (Complex.exp ((α : ℂ)*I))

/-- The phase part of Theorem 2(i) (p. 3), in complex Fréchet-covector form. -/
theorem theorem2_i_phase_covectors (k : ℕ) (hk : 1 ≤ k)
    (ab : SobolevSource (k-1)) (α : ℝ) :
    (fderiv ℂ (fun cd => sobolevNLSHamiltonian (k-1) cd k (by omega))
      (phaseRotation (k-1) α ab)).comp (phaseRotation (k-1) α) =
        fderiv ℂ (fun cd => sobolevNLSHamiltonian (k-1) cd k (by omega)) ab :=
  fderiv_sobolevNLSHamiltonian_reciprocal_scaling (k-1) k (by omega) ab
    (Complex.exp ((α : ℂ)*I)) (Complex.exp_ne_zero _)

end NLS.Articles.MKdVNLSHierarchies
