import NLS.DifferentialPolynomial.PeriodicEvaluation
import NLS.ZakharovShabat.NLSRiccatiPolynomials
import Mathlib.Analysis.Complex.RealDeriv

/-! # The physical KdV energy in the Hill Riccati coefficient

The constant-upper ZS specialization (a,b)=(-1,-q) has scalar potential
q. Its coefficient of inverse spectral order five has period integral
2*Hkdv(q). This is the physical coefficient calculation needed for (4.7)
of arXiv:1502.05857v1. It does not assert an analytic WKB expansion or a
Hill/ZS discriminant identification.
-/
noncomputable section
set_option autoImplicit false
open MvPolynomial Set Complex MeasureTheory
open scoped ContDiff
open NLS.DifferentialPolynomial NLS.ZakharovShabat
namespace NLS.KdV

/-- The actual complexified KdV energy, normalized on one spatial period. -/
def classicalHamiltonian (q : ℝ → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, (deriv q x) ^ 2 / 2 + (q x) ^ 3

/-- The lower physical invariant denoted H_0 in the article. -/
def classicalQuadraticInvariant (q : ℝ → ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∫ x in (0 : ℝ)..1, (q x) ^ 2

/-- The second polynomial in the existing Riccati recurrence. -/
theorem nlsRiccatiPolynomial_two : nlsRiccatiPolynomial 2 =
    -X (true,2) + X (false,0) * X (true,0) ^ 2 := by
  rw [show 2 = 0+2 from rfl, nlsRiccatiPolynomial_recurrence]
  simp [spatialDerivative_X, nextJet]
  ring

/-- The third polynomial, computed in the existing differential algebra. -/
theorem nlsRiccatiPolynomial_three : nlsRiccatiPolynomial 3 =
    -X (true,3) + X (false,1) * X (true,0) ^ 2 +
      4 * X (false,0) * X (true,0) * X (true,1) := by
  rw [nlsRiccatiPolynomial_recurrence 1]
  simp [Finset.Nat.antidiagonal_succ, nlsRiccatiPolynomial_two,
    Derivation.leibniz, Derivation.leibniz_pow, spatialDerivative_X, nextJet]
  ring

/-- The fourth polynomial includes all derivative terms; none are discarded
before taking its actual periodic integral. -/
theorem nlsRiccatiPolynomial_four : nlsRiccatiPolynomial 4 =
    -X (true,4) + X (false,2) * X (true,0) ^ 2 +
      6 * X (false,1) * X (true,0) * X (true,1) +
      5 * X (false,0) * X (true,1) ^ 2 +
      6 * X (false,0) * X (true,0) * X (true,2) -
      2 * X (false,0) ^ 2 * X (true,0) ^ 3 := by
  have h4 : spatialDerivative (4 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 4
  rw [nlsRiccatiPolynomial_recurrence 2]
  simp [Finset.Nat.antidiagonal_succ, nlsRiccatiPolynomial_two,
    nlsRiccatiPolynomial_three, Derivation.leibniz, Derivation.leibniz_pow,
    spatialDerivative_X, nextJet, h4]
  ring

/-- The scalar Hill coefficient obtained by the actual ZS specialization. -/
def hillEnergyDensity : DifferentialPolynomial.Polynomial :=
  X (false,4) - 5 * X (false,1) ^ 2 -
    6 * X (false,0) * X (false,2) + 2 * X (false,0) ^ 3

/-- An explicit total derivative balances the fifth-order Riccati density
into twice the physical KdV energy density. -/
theorem hillEnergyDensity_reduction : hillEnergyDensity =
    (X (false,1) ^ 2 + 2 * X (false,0) ^ 3) +
      spatialDerivative (X (false,3) - 6 * X (false,0) * X (false,1)) := by
  have h6 : spatialDerivative (6 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 6
  simp [hillEnergyDensity, Derivation.leibniz, spatialDerivative_X, nextJet, h6]
  ring

/-- Evaluating the existing Riccati density at the constant-upper
specialization gives the actual scalar Hill energy density. -/
theorem nlsRiccatiDensity_const_upper_four (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) :
    nlsRiccatiDensity (fun _ => -1) (-q) 4 =
      evaluate q 0 hillEnergyDensity := by
  rw [← evaluate_nlsRiccatiPolynomial (fun _ => -1) (-q) contDiff_const hq.neg,
    nlsRiccatiPolynomial_four]
  funext x
  simp [evaluate, hillEnergyDensity, iteratedDeriv_neg, iteratedDeriv_const]
  ring

/-- The Hill coefficient has period integral twice the actual KdV
energy for every smooth periodic complex potential. -/
theorem integral_hillEnergyDensity (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) :
    (∫ x in (0 : ℝ)..1, evaluate q 0 hillEnergyDensity x) =
      2 * classicalHamiltonian q := by
  have he := integral_evaluate_eq_of_total_derivative q 0 hq contDiff_const hp
    (fun _ => rfl) hillEnergyDensity
    (X (false,1) ^ 2 + 2 * X (false,0) ^ 3)
    (X (false,3) - 6 * X (false,0) * X (false,1)) hillEnergyDensity_reduction
  rw [he]
  unfold classicalHamiltonian
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  simp [evaluate, iteratedDeriv_one]
  ring

/-- The existing physical NLS hierarchy supplies the KdV energy coefficient
with its exact factor 2. No spectral or energy identity is assumed. -/
theorem classicalNLSHamiltonian_const_upper_five (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1) :
    classicalNLSHamiltonian (fun _ => -1) (-q) 5 = 2 * classicalHamiltonian q := by
  have he : classicalNLSHamiltonian (fun _ => -1) (-q) 5 =
      ∫ x in (0 : ℝ)..1, nlsRiccatiDensity (fun _ => -1) (-q) 4 x := by
    simp only [classicalNLSHamiltonian, neg_one_mul, intervalIntegral.integral_neg]
    norm_num [pow_succ, I_sq]
  rw [he, nlsRiccatiDensity_const_upper_four q hq]
  exact integral_hillEnergyDensity q hq hp

/-- The first specialized coefficient is the actual mean of q. -/
theorem classicalNLSHamiltonian_const_upper_one (q : ℝ → ℂ) :
    classicalNLSHamiltonian (fun _ => -1) (-q) 1 = ∫ x in (0 : ℝ)..1, q x := by
  simp [classicalNLSHamiltonian_one]

/-- The third specialized coefficient is twice the source invariant H_0. -/
theorem classicalNLSHamiltonian_const_upper_three (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1) :
    classicalNLSHamiltonian (fun _ => -1) (-q) 3 =
      2 * classicalQuadraticInvariant q := by
  rw [classicalNLSHamiltonian_three (fun _ => -1) (-q) contDiff_const hq.neg
    (fun _ => rfl) (fun x => by change -q (x+1) = -q x; rw [hp x])]
  simp [classicalQuadraticInvariant]

/-- The odd Riccati coefficient is an explicit total derivative. -/
def hillOddDensity : DifferentialPolynomial.Polynomial :=
  X (false,3) - 4 * X (false,0) * X (false,1)

theorem hillOddDensity_reduction : hillOddDensity =
    spatialDerivative (X (false,2) - 2 * X (false,0) ^ 2) := by
  have h2 : spatialDerivative (2 : DifferentialPolynomial.Polynomial) = 0 :=
    Derivation.map_natCast _ 2
  simp [hillOddDensity, Derivation.leibniz, Derivation.leibniz_pow,
    spatialDerivative_X, nextJet, h2]
  ring

theorem nlsRiccatiDensity_const_upper_three (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) :
    nlsRiccatiDensity (fun _ => -1) (-q) 3 = evaluate q 0 hillOddDensity := by
  rw [← evaluate_nlsRiccatiPolynomial (fun _ => -1) (-q) contDiff_const hq.neg,
    nlsRiccatiPolynomial_three]
  funext x
  simp [evaluate, hillOddDensity, iteratedDeriv_neg, iteratedDeriv_const]
  ring

/-- Both lower even-index NLS coefficients vanish by periodicity, with no
spectral-symmetry or discriminant-identification assumption. -/
theorem classicalNLSHamiltonian_const_upper_two (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1) :
    classicalNLSHamiltonian (fun _ => -1) (-q) 2 = 0 := by
  have hz : (∫ x in (0 : ℝ)..1, deriv q x) = 0 := by
    simpa [spatialDerivative_X, nextJet, evaluate, iteratedDeriv_one] using
      integral_evaluate_spatialDerivative q 0 hq contDiff_const hp (fun _ => rfl) (X (false,0))
  rw [classicalNLSHamiltonian_two_unsymmetrized]
  simp [hz]

theorem classicalNLSHamiltonian_const_upper_four (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1) :
    classicalNLSHamiltonian (fun _ => -1) (-q) 4 = 0 := by
  have hz : (∫ x in (0 : ℝ)..1, evaluate q 0 hillOddDensity x) = 0 := by
    rw [hillOddDensity_reduction]
    exact integral_evaluate_spatialDerivative q 0 hq contDiff_const hp (fun _ => rfl) _
  simp only [classicalNLSHamiltonian, nlsRiccatiDensity_const_upper_three q hq,
    neg_one_mul, intervalIntegral.integral_neg, hz, neg_zero, mul_zero]

/-- The first five physical coefficients have the normalization needed for
the mean-zero KdV high-energy expansion, calculated from actual integrals. -/
theorem classicalNLSHamiltonian_const_upper_first_five (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1)
    (hmean : (∫ x in (0 : ℝ)..1, q x) = 0) :
    classicalNLSHamiltonian (fun _ => -1) (-q) 1 = 0 ∧
    classicalNLSHamiltonian (fun _ => -1) (-q) 2 = 0 ∧
    classicalNLSHamiltonian (fun _ => -1) (-q) 3 = 2 * classicalQuadraticInvariant q ∧
    classicalNLSHamiltonian (fun _ => -1) (-q) 4 = 0 ∧
    classicalNLSHamiltonian (fun _ => -1) (-q) 5 = 2 * classicalHamiltonian q := by
  exact ⟨(classicalNLSHamiltonian_const_upper_one q).trans hmean,
    classicalNLSHamiltonian_const_upper_two q hq hp,
    classicalNLSHamiltonian_const_upper_three q hq hp,
    classicalNLSHamiltonian_const_upper_four q hq hp,
    classicalNLSHamiltonian_const_upper_five q hq hp⟩

/-- On real potentials the complexified definition is exactly the real
Hamiltonian printed in the article, with no conjugation or scaling change. -/
theorem classicalHamiltonian_ofReal (q : ℝ → ℝ) (hq : Differentiable ℝ q) :
    classicalHamiltonian (fun x => (q x : ℂ)) =
      ((∫ x in (0 : ℝ)..1, (deriv q x) ^ 2 / 2 + (q x) ^ 3 : ℝ) : ℂ) := by
  have hd : deriv (fun x => (q x : ℂ)) = fun x => Complex.ofReal (deriv q x) := by
    funext x
    exact ((hq x).hasDerivAt.ofReal_comp).deriv
  unfold classicalHamiltonian
  rw [hd, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x _
  push_cast
  rfl

end NLS.KdV
