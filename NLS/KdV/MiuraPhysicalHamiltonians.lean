import NLS.DifferentialPolynomial.ScalarHillRiccatiLowOrders
import NLS.DifferentialPolynomial.EulerLagrange
import NLS.MKdV.MiuraHierarchyHamiltonians
import NLS.KdV.NativeHamiltonianPhysicalIntegrals

/-! # Exact physical KdV Hamiltonians in the independent Miura hierarchy

Explicit total derivatives identify the scalar recurrence's third and
fourth Hamiltonians with the printed physical KdV and KdV2 integrals.
-/
noncomputable section
set_option autoImplicit false
open MvPolynomial Set Complex MeasureTheory
open scoped ContDiff
open NLS.DifferentialPolynomial NLS.MKdV
namespace NLS.KdV

/-- The second scalar coefficient integrates to the physical square. -/
theorem integral_scalarHillRiccati_two (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (P : DifferentialPolynomial.Polynomial) :
    (∫ x in (0 : ℝ)..1,
      evaluate a b (differentialRiccatiSequence spatialDerivative 1 P 2) x) =
      ∫ x in (0 : ℝ)..1, (evaluate a b P x)^2 := by
  have he : differentialRiccatiSequence spatialDerivative 1 P 2 =
      P^2+spatialDerivative (-spatialDerivative P) := by
    rw [scalarHillRiccati_two,map_neg]
    ring
  rw [integral_evaluate_eq_of_total_derivative a b ha hb hpa hpb _ _ _ he]
  apply intervalIntegral.integral_congr
  intro x _
  simp [evaluate]

/-- The fourth scalar coefficient has period integral minus twice H1. -/
theorem integral_scalarHillRiccati_four (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (P : DifferentialPolynomial.Polynomial) :
    (∫ x in (0 : ℝ)..1,
      evaluate a b (differentialRiccatiSequence spatialDerivative 1 P 4) x) =
      -2*classicalHamiltonian (evaluate a b P) := by
  have he := integral_evaluate_eq_of_total_derivative a b ha hb hpa hpb _ _ _
    (scalarHillRiccati_four_reduction spatialDerivative P)
  rw [he,classicalHamiltonian,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  have hd := congrFun (evaluate_spatialDerivative a b ha hb P) x
  simp only [evaluate] at hd ⊢
  simp only [eval_neg,eval_add,eval_mul,eval_pow,eval_ofNat]
  rw [hd]
  ring

/-- The sixth scalar coefficient has period integral twice H2. -/
theorem integral_scalarHillRiccati_six (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (P : DifferentialPolynomial.Polynomial) :
    (∫ x in (0 : ℝ)..1,
      evaluate a b (differentialRiccatiSequence spatialDerivative 1 P 6) x) =
      2*classicalKdV2Hamiltonian (evaluate a b P) := by
  have he := integral_evaluate_eq_of_total_derivative a b ha hb hpa hpb _ _ _
    (scalarHillRiccati_six_reduction spatialDerivative P)
  rw [he,classicalKdV2Hamiltonian,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  have hd := evaluate_spatialDerivative a b ha hb P
  have hdd := evaluate_spatialDerivative a b ha hb (spatialDerivative P)
  rw [hd] at hdd
  have hd' := congrFun hd x
  have hdd' := congrFun hdd x
  simp only [evaluate] at hd' hdd' ⊢
  simp only [eval_add,eval_mul,eval_pow,eval_ofNat]
  rw [hd',hdd']
  ring

/-- The actual smooth Miura potential, with the period-one derivative. -/
theorem evaluate_miuraHillPotentialPolynomial (u : ℝ → ℂ) :
    evaluate u u miuraHillPotentialPolynomial = fun x => deriv u x+(u x)^2 := by
  funext x
  simp [miuraHillPotentialPolynomial,evaluate,iteratedDeriv_one]

/-- The independent second scalar Hamiltonian is the physical mass of
its actual Miura potential. -/
theorem classicalMiuraHillHamiltonian_two_eq_miura_mass (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) :
    classicalMiuraHillHamiltonian u 2 =
      classicalMKdVMass (fun x => deriv u x+(u x)^2) := by
  change ((-1 : ℂ)^2/2)*
    (∫ x in (0 : ℝ)..1, evaluate u u (miuraHillRiccatiPolynomial 2) x) = _
  rw [miuraHillRiccatiPolynomial,integral_scalarHillRiccati_two u u hu hu hp hp,
    evaluate_miuraHillPotentialPolynomial,classicalMKdVMass]
  norm_num

/-- The independently defined third scalar Hamiltonian is exactly printed H1
of the actual Miura potential. -/
theorem classicalMiuraHillHamiltonian_three (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) :
    classicalMiuraHillHamiltonian u 3 =
      classicalHamiltonian (fun x => deriv u x+(u x)^2) := by
  change ((-1 : ℂ)^3/2)*
    (∫ x in (0 : ℝ)..1, evaluate u u (miuraHillRiccatiPolynomial 4) x) = _
  rw [miuraHillRiccatiPolynomial,integral_scalarHillRiccati_four u u hu hu hp hp,
    evaluate_miuraHillPotentialPolynomial]
  ring

/-- The independently defined fourth scalar Hamiltonian is exactly printed H2
of the actual Miura potential, with coefficients 1/2, 5 and 5/2. -/
theorem classicalMiuraHillHamiltonian_four (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hp : Function.Periodic u 1) :
    classicalMiuraHillHamiltonian u 4 =
      classicalKdV2Hamiltonian (fun x => deriv u x+(u x)^2) := by
  change ((-1 : ℂ)^4/2)*
    (∫ x in (0 : ℝ)..1, evaluate u u (miuraHillRiccatiPolynomial 6) x) = _
  rw [miuraHillRiccatiPolynomial,integral_scalarHillRiccati_six u u hu hu hp hp,
    evaluate_miuraHillPotentialPolynomial]
  ring

end NLS.KdV
