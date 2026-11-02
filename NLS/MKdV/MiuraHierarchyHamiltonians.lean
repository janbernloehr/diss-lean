import NLS.DifferentialPolynomial.MiuraRiccati
import NLS.DifferentialPolynomial.RiccatiResolventNaturality
import NLS.DifferentialPolynomial.MultiJet
import NLS.MKdV.HierarchyRestriction
import NLS.ZakharovShabat.NLSRiccatiResolvent

/-! # Independently constructed scalar Hill / Miura Hamiltonians

The scalar recurrence is rho₀=-q, rho₁=-Dq and
rhoₙ₊₂=D rhoₙ₊₁+sum rhoᵢ rhoⱼ, at the Miura potential q=u'+u².
Its even coefficients specify the Hamiltonians independently of the NLS
restriction. The all-order integral identity follows from the explicit
logarithmic gauge primitive, with no finite-gap hypothesis.

This is a smooth periodic statement. Identifying its sharp Sobolev
extensions and the article's spectral mKdV actions is separate work.
-/
noncomputable section
open MvPolynomial Complex NLS.DifferentialPolynomial NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.MKdV

/-- The scalar Hill potential under the Miura map, in one field's jets. -/
def miuraHillPotentialPolynomial : DifferentialPolynomial.Polynomial :=
  X (false,1)+X (false,0)^2

/-- Scalar Hill Riccati densities, independently seeded by -(u'+u²). -/
def miuraHillRiccatiPolynomial (n : ℕ) : DifferentialPolynomial.Polynomial :=
  differentialRiccatiSequence spatialDerivative 1 miuraHillPotentialPolynomial n

/-- The scalar Hamiltonians from the even Hill Riccati coefficients. -/
def classicalMiuraHillHamiltonian (u : ℝ → ℂ) : ℕ → ℂ
  | 0 => 0
  | m+1 => ((-1 : ℂ)^(m+1)/2)*
      ∫ x in (0 : ℝ)..1, evaluate u u (miuraHillRiccatiPolynomial (2*m)) x

def miuraDiagonalPolynomialMap : DifferentialPolynomial.Polynomial →ₐ[ℂ]
    DifferentialPolynomial.Polynomial := renameFields (fun _ : Bool => false)

private theorem miuraDiagonalPolynomialMap_D (p : DifferentialPolynomial.Polynomial) :
    miuraDiagonalPolynomialMap (spatialDerivative p) = spatialDerivative (miuraDiagonalPolynomialMap p) :=
  renameFields_spatialDerivative (fun _ : Bool => false) p

private theorem miuraDiagonalPolynomialMap_X (v : Jet) : miuraDiagonalPolynomialMap (X v) = X (false,v.2) := by
  simp [miuraDiagonalPolynomialMap, renameFields]

private theorem miuraDiagonalPolynomialMap_nlsRiccatiPolynomial (n : ℕ) :
    miuraDiagonalPolynomialMap (nlsRiccatiPolynomial n) =
      differentialRiccatiSequence spatialDerivative (X (false,0)) (X (false,0)) n := by
  rw [nlsRiccatiPolynomial_eq_differentialRiccatiSequence]
  have he := map_differentialRiccatiSequence spatialDerivative spatialDerivative
    miuraDiagonalPolynomialMap.toRingHom miuraDiagonalPolynomialMap_D (X (false,0)) (X (true,0)) n
  change miuraDiagonalPolynomialMap _ = differentialRiccatiSequence spatialDerivative
    (miuraDiagonalPolynomialMap (X (false,0))) (miuraDiagonalPolynomialMap (X (true,0))) n at he
  simpa only [miuraDiagonalPolynomialMap_X] using he

private theorem evaluate_miuraDiagonalPolynomialMap (u : ℝ → ℂ) (p : DifferentialPolynomial.Polynomial) :
    evaluate u u (miuraDiagonalPolynomialMap p) = evaluate u u p := by
  funext x
  change MvPolynomial.eval₂ (RingHom.id ℂ) _ (MvPolynomial.rename _ p) = _
  rw [MvPolynomial.eval₂_rename]
  simp only [evaluate, Function.comp_def, ite_self]
  rfl

/-- An explicit polynomial primitive compares each independently constructed
scalar Hill density with the corresponding physical diagonal NLS density. -/
theorem miuraHillRiccatiPolynomial_eq_diagonal_plus_derivative (n : ℕ) :
    miuraHillRiccatiPolynomial n =
      miuraDiagonalPolynomialMap (X (false,0)*nlsRiccatiPolynomial n) +
        spatialDerivative (logarithmicPrimitiveCoefficient (K := ℂ)
          (differentialRiccatiSeries spatialDerivative (X (false,0)) (X (false,0))) n) := by
  rw [map_mul, miuraDiagonalPolynomialMap_X, miuraDiagonalPolynomialMap_nlsRiccatiPolynomial]
  have he := differentialRiccatiSequence_miura spatialDerivative (X (false,0)) n
  simpa only [miuraHillRiccatiPolynomial, miuraHillPotentialPolynomial,
    spatialDerivative_X, nextJet] using he

/-- All-order equality of the actual periodic integrals, rather than a
definition of the scalar densities by an NLS restriction. -/
theorem integral_miuraHillRiccatiPolynomial (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) (n : ℕ) :
    (∫ x in (0 : ℝ)..1, evaluate u u (miuraHillRiccatiPolynomial n) x) =
      ∫ x in (0 : ℝ)..1, u x*nlsRiccatiDensity u u n x := by
  rw [integral_evaluate_eq_of_total_derivative u u hu hu hp hp _ _ _
    (miuraHillRiccatiPolynomial_eq_diagonal_plus_derivative n), evaluate_miuraDiagonalPolynomialMap,
    evaluate_mul, evaluate_X, evaluate_nlsRiccatiPolynomial u u hu hu]
  rfl

/-- Proposition 6's factor of two, at all orders for the independently
constructed scalar Hill Hamiltonians on smooth complex periodic fields. -/
theorem classicalNLSHamiltonian_odd_diagonal_eq_miuraHill (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) (m : ℕ) :
    classicalNLSHamiltonian u u (2*m+1) = 2*classicalMiuraHillHamiltonian u (m+1) := by
  have hc : (-I)^(2*m+2) = (-1 : ℂ)^(m+1) := by
    rw [show 2*m+2 = 2*(m+1) by omega, pow_mul]
    congr 1
    norm_num [I_sq]
  rw [classicalNLSHamiltonian, classicalMiuraHillHamiltonian,
    integral_miuraHillRiccatiPolynomial u hu hp, hc]
  ring

theorem classicalMiuraHillHamiltonian_one (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) :
    classicalMiuraHillHamiltonian u 1 = classicalMKdVMass u := by
  have he := classicalNLSHamiltonian_odd_diagonal_eq_miuraHill u hu hp 0
  rw [classicalNLSHamiltonian_one_diagonal] at he
  linear_combination -(1/2 : ℂ)*he

theorem classicalMiuraHillHamiltonian_two (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) :
    classicalMiuraHillHamiltonian u 2 = classicalMKdVEnergy u := by
  have he := classicalNLSHamiltonian_odd_diagonal_eq_miuraHill u hu hp 1
  rw [classicalNLSHamiltonian_three_diagonal u hu hp] at he
  linear_combination -(1/2 : ℂ)*he

/-- The scalar part of Theorem 1 at every smooth periodic order. -/
theorem classicalNLSHamiltonian_even_diagonal_eq_zero (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) (m : ℕ) :
    classicalNLSHamiltonian u u (2*m+2) = 0 := by
  have hs := classicalNLSHamiltonian_signedSwap u u hu hu hp hp (2*m+1)
  have hn : classicalNLSHamiltonian (-u) (-u) (2*m+2) =
      classicalNLSHamiltonian u u (2*m+2) := by
    simpa only [neg_one_smul, neg_neg] using
      classicalNLSHamiltonian_field_rescaling (-u) u (-1) (2*m+2)
  rw [show 2*m+1+1 = 2*m+2 by omega, hn, pow_succ, pow_mul, neg_one_sq,
    one_pow, one_mul, neg_one_mul] at hs
  linear_combination (1/2 : ℂ)*hs

end NLS.MKdV
