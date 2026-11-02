import NLS.Articles.MKdVNLSHierarchies.SharpEvenVanishing
import NLS.MKdV.SobolevMiuraHillFlowRestriction

/-! # Theorem 1 on complex H^m for the independent scalar Hill hierarchy

Both clauses use the exact input domain and actual physical weak vector
fields. The scalar hierarchy is constructed from the Hill Riccati densities.
Its remaining source spectral identification is recorded in the coverage
report; no independent spectral action comparison is asserted here.
-/
noncomputable section
open NLS.MKdV NLS.ZakharovShabat NLS.Fourier
namespace NLS.Articles.MKdVNLSHierarchies

/-- The full H^m weak flow identity and scalar vanishing, for every integer
m>=1 and every complex u, for the independently specified Hill/Miura hierarchy.
The scalar gradient is an actual Fréchet gradient and its derivative is
Mathlib's genuine distribution derivative, represented by the even field. -/
theorem theorem1_sharp_miura_hierarchy (m : ℕ) (hm : 1 ≤ m) (u : ScalarSobolev m) :
    sobolevEvenHamiltonian m hm (u,u) = 0 ∧
      (periodOneSobolevDistribution (-(m : ℝ)) (sobolevEvenHierarchyVectorField m hm (u,u)).1,
        periodOneSobolevDistribution (-(m : ℝ)) (sobolevEvenHierarchyVectorField m hm (u,u)).2) =
          (sobolevMiuraHillVectorField m hm u, sobolevMiuraHillVectorField m hm u) :=
  ⟨theorem1_even_vanishing_sharp m hm u, sobolevMiuraHillFlowRestriction m hm u⟩

end NLS.Articles.MKdVNLSHierarchies
