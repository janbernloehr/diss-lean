import NLS.KdV.HillRiccatiHierarchy

/-! # Explicit scalar densities through order seven and the physical second Hamiltonian, with its exact coefficients. -/

noncomputable section
set_option autoImplicit false
open MvPolynomial Complex MeasureTheory NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.KdV

theorem hillRiccatiPolynomial_two : hillRiccatiPolynomial 2 =
    X (false,2)-X (false,0)^2 := by
  rw [hillRiccatiPolynomial_recurrence 0]
  simp [spatialDerivative_X, nextJet]
  ring

theorem hillRiccatiPolynomial_three : hillRiccatiPolynomial 3 =
    -X (false,3)+4*X (false,0)*X (false,1) := by
  rw [hillRiccatiPolynomial_recurrence 1]
  simp [Finset.Nat.antidiagonal_succ, hillRiccatiPolynomial_two,
    Derivation.leibniz_pow, spatialDerivative_X, nextJet]
  ring

theorem hillRiccatiPolynomial_four : hillRiccatiPolynomial 4 = hillEnergyDensity := by
  rw [hillRiccatiPolynomial_recurrence 2]
  have h4 : spatialDerivative (4 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 4
  simp [Finset.Nat.antidiagonal_succ, hillRiccatiPolynomial_two,
    hillRiccatiPolynomial_three, hillEnergyDensity, Derivation.leibniz, spatialDerivative_X, nextJet, h4]
  ring

theorem hillRiccatiPolynomial_five : hillRiccatiPolynomial 5 =
    -X (false,5)+18*X (false,1)*X (false,2)+8*X (false,0)*X (false,3)-
      16*X (false,0)^2*X (false,1) := by
  rw [hillRiccatiPolynomial_recurrence 3]
  have h5 : spatialDerivative (5 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 5
  have h6 : spatialDerivative (6 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 6
  have h2 : spatialDerivative (2 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 2
  simp [Finset.Nat.antidiagonal_succ, hillRiccatiPolynomial_two,
    hillRiccatiPolynomial_three, hillRiccatiPolynomial_four, hillEnergyDensity,
    Derivation.leibniz, Derivation.leibniz_pow, spatialDerivative_X, nextJet, h5,h6,h2]
  ring

theorem hillRiccatiPolynomial_six : hillRiccatiPolynomial 6 =
    X (false,6)-19*X (false,2)^2-28*X (false,1)*X (false,3)-
      10*X (false,0)*X (false,4)+50*X (false,0)*X (false,1)^2+
      30*X (false,0)^2*X (false,2)-5*X (false,0)^4 := by
  rw [hillRiccatiPolynomial_recurrence 4]
  have h18 : spatialDerivative (18 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 18
  have h8 : spatialDerivative (8 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 8
  have h16 : spatialDerivative (16 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 16
  simp [Finset.Nat.antidiagonal_succ, hillRiccatiPolynomial_two,
    hillRiccatiPolynomial_three, hillRiccatiPolynomial_four, hillRiccatiPolynomial_five,
    hillEnergyDensity, Derivation.leibniz, Derivation.leibniz_pow,
    spatialDerivative_X, nextJet, h18,h8,h16]
  ring

def hillSecondHamiltonianDensity : DifferentialPolynomial.Polynomial :=
  X (false,2)^2+10*X (false,0)*X (false,1)^2+5*X (false,0)^4

def hillSecondHamiltonianPrimitive : DifferentialPolynomial.Polynomial :=
  X (false,5)-10*X (false,0)*X (false,3)-18*X (false,1)*X (false,2)+
    30*X (false,0)^2*X (false,1)

theorem hillRiccatiPolynomial_six_reduction : hillRiccatiPolynomial 6 =
    -hillSecondHamiltonianDensity+spatialDerivative hillSecondHamiltonianPrimitive := by
  have h10 : spatialDerivative (10 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 10
  have h18 : spatialDerivative (18 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 18
  have h30 : spatialDerivative (30 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 30
  simp [hillRiccatiPolynomial_six, hillSecondHamiltonianDensity,
    hillSecondHamiltonianPrimitive, Derivation.leibniz, Derivation.leibniz_pow,
    spatialDerivative_X, nextJet, h10,h18,h30]
  ring

theorem classicalKdVHierarchyHamiltonian_two (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) :
    classicalKdVHierarchyHamiltonian q 2 = (1/2 : ℂ)*∫ x in (0 : ℝ)..1,
      (iteratedDeriv 2 q x)^2+10*q x*(deriv q x)^2+5*(q x)^4 := by
  have he := integral_evaluate_eq_of_total_derivative q 0 hq contDiff_const hp
    (fun _ => rfl) _ (-hillSecondHamiltonianDensity) hillSecondHamiltonianPrimitive
    hillRiccatiPolynomial_six_reduction
  simp only [classicalKdVHierarchyHamiltonian, show 2*2+2 = 6 by omega]
  rw [he]
  simp only [evaluate_neg, Pi.neg_apply, intervalIntegral.integral_neg]
  norm_num
  congr 1
  funext x
  simp [hillSecondHamiltonianDensity, evaluate, iteratedDeriv_one]

end NLS.KdV
