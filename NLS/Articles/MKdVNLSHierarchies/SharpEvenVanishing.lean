import NLS.ZakharovShabat.SobolevEvenHamiltonian

/-! # The scalar clause of Theorem 1 on its exact complex Sobolev domain -/
noncomputable section
open NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

/-- For every m>=1, the actual analytic extension of S_(2m) to complex
H^m vanishes at every diagonal input, including nonsmooth ones. Its agreement
with the original hierarchy is `sobolevEvenHamiltonian_eq_original`. -/
theorem theorem1_even_vanishing_sharp (m : ℕ) (hm : 1 ≤ m) (u : ScalarSobolev m) :
    sobolevEvenHamiltonian m hm (u,u) = 0 := by
  have he := sobolevEvenHamiltonian_swap m hm (u,u)
  linear_combination (1/2 : ℂ)*he

end NLS.Articles.MKdVNLSHierarchies
