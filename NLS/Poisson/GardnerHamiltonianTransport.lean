import NLS.Poisson.GardnerBracketJacobi
import NLS.Poisson.GardnerHamiltonianZeroMode
import NLS.Poisson.ConstantOperatorJacobi

noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal

namespace NLS.Poisson



/-- The existing actual scalar Gardner Hamiltonian operator is skew on
original H-minus-one differentials. -/
theorem gardnerHamiltonianDirection_skew
    (L M : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    L (gardnerHamiltonianDirection M)= -M (gardnerHamiltonianDirection L) := by
  rw [apply_gardnerHamiltonianDirection,apply_gardnerHamiltonianDirection]
  exact gardnerCotangentBivector_antisymm _ _

/-- The physical scalar Gardner bracket is the bracket of the existing
fixed bounded Hamiltonian operator on its H-minus-one Banach space. -/
theorem hminusGardnerBracket_eq_constantOperatorBracket :
    hminusGardnerBracket=constantOperatorBracket gardnerHamiltonianDirection := by
  funext F G q
  exact (apply_gardnerHamiltonianDirection (fderiv ℂ F q) (fderiv ℂ G q)).symm

/-- Exact infinitesimal transport of the actual scalar Gardner bracket
along its actual Hamiltonian source direction. -/
theorem hminusGardnerBracket_hamiltonian_derivative
    (F G H : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2)
    (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q) (hH : AnalyticAt ℂ H q) :
    (fderiv ℂ (hminusGardnerBracket F G) q) (gardnerHamiltonianVector H q)=
      (fderiv ℂ (hminusGardnerBracket F H) q) (gardnerHamiltonianVector G q)-
        (fderiv ℂ (hminusGardnerBracket G H) q) (gardnerHamiltonianVector F q) := by
  rw [hminusGardnerBracket_eq_constantOperatorBracket]
  exact constantOperatorBracket_hamiltonian_derivative gardnerHamiltonianDirection
    gardnerHamiltonianDirection_skew F G H q hF hG hH

end NLS.Poisson
