import NLS.DifferentialPolynomial.PeriodicEvaluation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Smooth identities for the actual KdV and KdV2 equations

Source: arXiv:1605.06690v1, equations (1)-(3), PDF pp. 1-2, and the
nonzero-mean reduction in Remarks 3.7(ii) and 4.6(ii), pp. 32 and 44.
We reuse the existing spatial jet derivation, evaluation on genuine smooth
functions and periodic integration theorem. These are physical differential
identities; they do not construct the spectral Birkhoff map or its frequencies.
-/

noncomputable section
set_option autoImplicit false
open MvPolynomial NLS.DifferentialPolynomial
open scoped ContDiff

namespace NLS.Articles.KdVKdV2Frequencies

@[simp] private theorem scalarDerivation_2 (D : Derivation ℂ Polynomial Polynomial) :
    D (2 : Polynomial) = 0 := D.map_natCast 2

@[simp] private theorem scalarDerivation_3 (D : Derivation ℂ Polynomial Polynomial) :
    D (3 : Polynomial) = 0 := D.map_natCast 3

@[simp] private theorem scalarDerivation_4 (D : Derivation ℂ Polynomial Polynomial) :
    D (4 : Polynomial) = 0 := D.map_natCast 4

@[simp] private theorem scalarDerivation_5 (D : Derivation ℂ Polynomial Polynomial) :
    D (5 : Polynomial) = 0 := D.map_natCast 5

@[simp] private theorem scalarDerivation_10 (D : Derivation ℂ Polynomial Polynomial) :
    D (10 : Polynomial) = 0 := D.map_natCast 10

@[simp] private theorem scalarDerivation_15 (D : Derivation ℂ Polynomial Polynomial) :
    D (15 : Polynomial) = 0 := D.map_natCast 15

@[simp] private theorem scalarDerivation_20 (D : Derivation ℂ Polynomial Polynomial) :
    D (20 : Polynomial) = 0 := D.map_natCast 20

/-- The kth derivative of the scalar KdV field in the existing jet algebra. -/
abbrev scalarJet (k : ℕ) : Polynomial := X (false, k)

/-- Twice the KdV Hamiltonian density; the source Hamiltonian has prefactor 1/2. -/
def twiceKdVDensity : Polynomial := scalarJet 1 ^ 2 + 2 * scalarJet 0 ^ 3

/-- Twice the KdV2 Hamiltonian density, with the same source prefactor 1/2. -/
def twiceKdV2Density : Polynomial :=
  scalarJet 2 ^ 2 + 10 * scalarJet 0 * scalarJet 1 ^ 2 + 5 * scalarJet 0 ^ 4

/-- Euler-Lagrange gradient polynomial of the source KdV Hamiltonian. -/
def kdvGradient : Polynomial := -scalarJet 2 + 3 * scalarJet 0 ^ 2

/-- Euler-Lagrange gradient polynomial of the source KdV2 Hamiltonian. -/
def kdv2Gradient : Polynomial :=
  scalarJet 4 - 10 * scalarJet 0 * scalarJet 2 - 5 * scalarJet 1 ^ 2 + 10 * scalarJet 0 ^ 3

/-- The literal right side of equation (1), as a jet polynomial. -/
def kdvVectorField : Polynomial := -scalarJet 3 + 6 * scalarJet 0 * scalarJet 1

/-- The literal right side of equation (2), as a jet polynomial. -/
def kdv2VectorField : Polynomial :=
  scalarJet 5 - 10 * scalarJet 0 * scalarJet 3 - 20 * scalarJet 1 * scalarJet 2 +
    30 * scalarJet 0 ^ 2 * scalarJet 1

/-- The Euler-Lagrange expression for the doubled first density is twice the
stated gradient; this retains the source Hamiltonian's factor 1/2. -/
theorem euler_twiceKdVDensity :
    pderiv (false, 0) twiceKdVDensity -
      spatialDerivative (pderiv (false, 1) twiceKdVDensity) = 2 * kdvGradient := by
  simp [twiceKdVDensity, kdvGradient,
    Derivation.leibniz, nextJet, smul_eq_mul, nsmul_eq_mul]
  ring

/-- The second density has jets only through order two, so its Euler-Lagrange
operator has these three terms and equals twice the stated gradient. -/
theorem euler_twiceKdV2Density :
    pderiv (false, 0) twiceKdV2Density -
      spatialDerivative (pderiv (false, 1) twiceKdV2Density) +
      spatialDerivative (spatialDerivative (pderiv (false, 2) twiceKdV2Density)) =
        2 * kdv2Gradient := by
  simp [twiceKdV2Density, kdv2Gradient,
    Derivation.leibniz, nextJet, smul_eq_mul, nsmul_eq_mul]
  ring

/-- Applying the Gardner spatial derivative gives precisely the KdV equation. -/
theorem spatialDerivative_kdvGradient : spatialDerivative kdvGradient = kdvVectorField := by
  simp [kdvGradient, kdvVectorField, Derivation.leibniz, nextJet,
    smul_eq_mul, nsmul_eq_mul]
  ring

/-- Applying the Gardner spatial derivative gives precisely the KdV2 equation. -/
theorem spatialDerivative_kdv2Gradient : spatialDerivative kdv2Gradient = kdv2VectorField := by
  simp [kdv2Gradient, kdv2VectorField, Derivation.leibniz, nextJet,
    smul_eq_mul, nsmul_eq_mul]
  ring

/-- Physical KdV right side on a scalar function of the period-one coordinate. -/
def kdvRHS (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  -iteratedDeriv 3 u x + 6 * u x * iteratedDeriv 1 u x

/-- Physical KdV2 right side with all printed coefficients and derivative signs. -/
def kdv2RHS (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  iteratedDeriv 5 u x - 10 * u x * iteratedDeriv 3 u x -
    20 * iteratedDeriv 1 u x * iteratedDeriv 2 u x +
      30 * u x ^ 2 * iteratedDeriv 1 u x

@[simp] theorem evaluate_kdvVectorField (u : ℝ → ℂ) (x : ℝ) :
    evaluate u 0 kdvVectorField x = kdvRHS u x := by
  simp [evaluate, kdvVectorField, kdvRHS]

@[simp] theorem evaluate_kdv2VectorField (u : ℝ → ℂ) (x : ℝ) :
    evaluate u 0 kdv2VectorField x = kdv2RHS u x := by
  simp [evaluate, kdv2VectorField, kdv2RHS]

/-- A genuine smooth-function derivative realizes the Hamiltonian KdV right side. -/
theorem hasDerivAt_evaluate_kdvGradient (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (x : ℝ) :
    HasDerivAt (evaluate u 0 kdvGradient) (kdvRHS u x) x := by
  simpa only [spatialDerivative_kdvGradient, evaluate_kdvVectorField] using
    hasDerivAt_evaluate u 0 hu contDiff_const kdvGradient x

/-- The same identity for the fifth-order KdV2 equation, on actual smooth fields. -/
theorem hasDerivAt_evaluate_kdv2Gradient (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (x : ℝ) :
    HasDerivAt (evaluate u 0 kdv2Gradient) (kdv2RHS u x) x := by
  simpa only [spatialDerivative_kdv2Gradient, evaluate_kdv2VectorField] using
    hasDerivAt_evaluate u 0 hu contDiff_const kdv2Gradient x

/-- Mean-shift identity underlying the KdV extension to nonzero symplectic leaves. -/
theorem kdvRHS_const_add (u : ℝ → ℂ) (c : ℂ) (x : ℝ) :
    kdvRHS (fun y => c + u y) x = kdvRHS u x + 6 * c * iteratedDeriv 1 u x := by
  simp only [kdvRHS, iteratedDeriv_const_add (by norm_num : 0 < 3),
    iteratedDeriv_const_add (by norm_num : 0 < 1)]
  ring

/-- The exact KdV2 nonzero-mean reduction: 10c times KdV and the translation term. -/
theorem kdv2RHS_const_add (u : ℝ → ℂ) (c : ℂ) (x : ℝ) :
    kdv2RHS (fun y => c + u y) x =
      kdv2RHS u x + 10 * c * kdvRHS u x + 30 * c ^ 2 * iteratedDeriv 1 u x := by
  simp only [kdv2RHS, kdvRHS, iteratedDeriv_const_add (by norm_num : 0 < 5),
    iteratedDeriv_const_add (by norm_num : 0 < 3),
    iteratedDeriv_const_add (by norm_num : 0 < 2),
    iteratedDeriv_const_add (by norm_num : 0 < 1)]
  ring

/-- Doubled local flux for the quadratic mass balance of KdV. -/
def twiceKdVMassFlux : Polynomial :=
  -2 * scalarJet 0 * scalarJet 2 + scalarJet 1 ^ 2 + 4 * scalarJet 0 ^ 3

/-- Doubled local flux for the quadratic mass balance of KdV2. -/
def twiceKdV2MassFlux : Polynomial :=
  2 * scalarJet 0 * scalarJet 4 - 2 * scalarJet 1 * scalarJet 3 + scalarJet 2 ^ 2 -
    20 * scalarJet 0 ^ 2 * scalarJet 2 + 15 * scalarJet 0 ^ 4

theorem spatialDerivative_twiceKdVMassFlux :
    spatialDerivative twiceKdVMassFlux = 2 * scalarJet 0 * kdvVectorField := by
  simp [twiceKdVMassFlux, kdvVectorField, Derivation.leibniz, nextJet,
    smul_eq_mul, nsmul_eq_mul]
  ring

theorem spatialDerivative_twiceKdV2MassFlux :
    spatialDerivative twiceKdV2MassFlux = 2 * scalarJet 0 * kdv2VectorField := by
  simp [twiceKdV2MassFlux, kdv2VectorField, Derivation.leibniz, nextJet,
    smul_eq_mul, nsmul_eq_mul]
  ring

/-- The actual KdV velocity has zero mean on every smooth period-one field. -/
theorem integral_kdvRHS_eq_zero (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hperiod : Function.Periodic u 1) : (∫ x in (0 : ℝ)..1, kdvRHS u x) = 0 := by
  simpa only [spatialDerivative_kdvGradient, evaluate_kdvVectorField] using
    integral_evaluate_spatialDerivative u 0 hu contDiff_const hperiod
      (fun _ => rfl) kdvGradient

/-- The same mean balance for the actual KdV2 velocity. -/
theorem integral_kdv2RHS_eq_zero (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hperiod : Function.Periodic u 1) : (∫ x in (0 : ℝ)..1, kdv2RHS u x) = 0 := by
  simpa only [spatialDerivative_kdv2Gradient, evaluate_kdv2VectorField] using
    integral_evaluate_spatialDerivative u 0 hu contDiff_const hperiod
      (fun _ => rfl) kdv2Gradient

/-- The integral pairing giving the time derivative of H0 vanishes for KdV.
This is a smooth spatial balance identity; differentiating a solution's
time-dependent integral is a separate analytic step. -/
theorem integral_mul_kdvRHS_eq_zero (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hperiod : Function.Periodic u 1) : (∫ x in (0 : ℝ)..1, u x * kdvRHS u x) = 0 := by
  have h := integral_evaluate_spatialDerivative u 0 hu contDiff_const hperiod
    (fun _ => rfl) twiceKdVMassFlux
  rw [spatialDerivative_twiceKdVMassFlux] at h
  have he (x : ℝ) : evaluate u 0 (2 * scalarJet 0 * kdvVectorField) x =
      2 * (u x * kdvRHS u x) := by
    calc
      _ = 2 * u x * evaluate u 0 kdvVectorField x := by simp [evaluate]
      _ = _ := by rw [evaluate_kdvVectorField]; ring
  simp_rw [he] at h
  rw [intervalIntegral.integral_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

/-- The quadratic mass pairing vanishes for the literal fifth-order equation. -/
theorem integral_mul_kdv2RHS_eq_zero (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hperiod : Function.Periodic u 1) : (∫ x in (0 : ℝ)..1, u x * kdv2RHS u x) = 0 := by
  have h := integral_evaluate_spatialDerivative u 0 hu contDiff_const hperiod
    (fun _ => rfl) twiceKdV2MassFlux
  rw [spatialDerivative_twiceKdV2MassFlux] at h
  have he (x : ℝ) : evaluate u 0 (2 * scalarJet 0 * kdv2VectorField) x =
      2 * (u x * kdv2RHS u x) := by
    calc
      _ = 2 * u x * evaluate u 0 kdv2VectorField x := by simp [evaluate]
      _ = _ := by rw [evaluate_kdv2VectorField]; ring
  simp_rw [he] at h
  rw [intervalIntegral.integral_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

end NLS.Articles.KdVKdV2Frequencies
