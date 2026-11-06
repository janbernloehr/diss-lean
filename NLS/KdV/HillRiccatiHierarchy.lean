import NLS.DifferentialPolynomial.UngradedIntegrationByParts
import NLS.DifferentialPolynomial.EulerOrderBounds
import NLS.KdV.MiuraPhysicalHamiltonians

/-! # The independently constructed original scalar KdV hierarchy

The scalar Hill recurrence is seeded by the original potential q, rather
than a Miura factor. Removing its explicit total derivative gives the
sharp derivative count needed for the original H^m domain.
-/
noncomputable section
set_option autoImplicit false
open MvPolynomial Set Complex MeasureTheory
open NLS.DifferentialPolynomial NLS.MKdV
open scoped ContDiff
namespace NLS.KdV

/-- The original scalar Hill recurrence at q. -/
def hillRiccatiPolynomial (n : ℕ) : DifferentialPolynomial.Polynomial :=
  differentialRiccatiSequence spatialDerivative 1 (X (false,0)) n

/-- The physical Hamiltonian H_m, specified independently by the scalar
recurrence with its exact original low-order normalizations. -/
def classicalHillHierarchyHamiltonian (q : ℝ → ℂ) (m : ℕ) : ℂ :=
  ((-1 : ℂ)^(m+2)/2)*∫ x in (0 : ℝ)..1, evaluate q q (hillRiccatiPolynomial (2*m+2)) x

/-- Every coefficient has at most its index in spatial derivatives. -/
theorem hillRiccatiPolynomial_derivativeOrder (n : ℕ) :
    DerivativeOrderLE (hillRiccatiPolynomial n) (n : ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa only [hillRiccatiPolynomial,differentialRiccatiSequence_zero] using
        (DerivativeOrderLE.X (false,0)).neg
    · simpa [hillRiccatiPolynomial] using
        (DerivativeOrderLE.X (false,0)).neg.spatialDerivative
    · rw [hillRiccatiPolynomial,differentialRiccatiSequence_recurrence,one_mul]
      apply DerivativeOrderLE.add
      · exact ((ih (n+1) (by omega)).spatialDerivative).mono (by push_cast; omega)
      · apply DerivativeOrderLE.sum
        intro ij hij
        have he := Finset.mem_antidiagonal.mp hij
        exact ((ih ij.1 (by omega)).mul (ih ij.2 (by omega))).mono (by push_cast; omega)

/-- The remainder after removing the highest linear total derivative. -/
def hillRiccatiRemainder (n : ℕ) : DifferentialPolynomial.Polynomial :=
  ∑ ij ∈ Finset.antidiagonal n, hillRiccatiPolynomial ij.1*hillRiccatiPolynomial ij.2

theorem hillRiccatiPolynomial_remainder (n : ℕ) :
    hillRiccatiPolynomial (n+2) = hillRiccatiRemainder n+
      spatialDerivative (hillRiccatiPolynomial (n+1)) := by
  rw [hillRiccatiPolynomial,differentialRiccatiSequence_recurrence,one_mul]
  exact add_comm _ _

theorem hillRiccatiRemainder_derivativeOrder (n : ℕ) :
    DerivativeOrderLE (hillRiccatiRemainder n) (n : ℤ) := by
  apply DerivativeOrderLE.sum
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  exact ((hillRiccatiPolynomial_derivativeOrder ij.1).mul
    (hillRiccatiPolynomial_derivativeOrder ij.2)).mono (by omega)

/-- The physical density H_m with its discarded derivative already removed. -/
def hillHierarchyNativeDensity (m : ℕ) : DifferentialPolynomial.Polynomial :=
  C ((-1 : ℂ)^(m+2)/2)*hillRiccatiRemainder (2*m)

theorem hillHierarchyNativeDensity_derivativeOrder (m : ℕ) :
    DerivativeOrderLE (hillHierarchyNativeDensity m) (2*(m : ℤ)) := by
  simpa only [hillHierarchyNativeDensity,zero_add,Nat.cast_mul,Nat.cast_ofNat] using
    (DerivativeOrderLE.C ((-1 : ℂ)^(m+2)/2)).mul (hillRiccatiRemainder_derivativeOrder (2*m))

/-- The removed derivative has this literal polynomial primitive. -/
theorem hillHierarchyNativeDensity_reduction (m : ℕ) :
    C ((-1 : ℂ)^(m+2)/2)*hillRiccatiPolynomial (2*m+2) =
      hillHierarchyNativeDensity m+
        spatialDerivative (C ((-1 : ℂ)^(m+2)/2)*hillRiccatiPolynomial (2*m+1)) := by
  rw [hillRiccatiPolynomial_remainder]
  simp only [hillHierarchyNativeDensity,Derivation.leibniz,MvPolynomial.derivation_C,
    smul_eq_mul,mul_zero,add_zero]
  ring

/-- Integration removes only an explicitly verified physical total derivative. -/
theorem integral_hillHierarchyNativeDensity (m : ℕ) (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1) :
    (∫ x in (0 : ℝ)..1, evaluate q q (hillHierarchyNativeDensity m) x) =
      classicalHillHierarchyHamiltonian q m := by
  rw [←integral_evaluate_eq_of_total_derivative q q hq hq hp hp _ _ _
    (hillHierarchyNativeDensity_reduction m)]
  simp only [evaluate_mul,evaluate_C,Pi.mul_apply]
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- Each original hierarchy member has one native density with exactly the
endpoint jet and derivative bounds, chosen before the physical source. -/
theorem exists_hillHierarchyNativePolynomial (m : ℕ) :
    ∃ P : DifferentialPolynomial.Polynomial, JetOrderLE P m ∧
      DerivativeOrderLE P (2*(m : ℤ)) ∧
      ∀ q : ℝ → ℂ, ContDiff ℝ ∞ q → Function.Periodic q 1 →
        classicalHillHierarchyHamiltonian q m = ∫ x in (0 : ℝ)..1, evaluate q q P x := by
  obtain ⟨P,R,he,hP,hD⟩ := exists_jet_reduction_of_derivativeOrder (m+1) (by omega)
    (hillHierarchyNativeDensity m) (2*(m : ℤ)) (by push_cast; omega)
    (hillHierarchyNativeDensity_derivativeOrder m)
  refine ⟨P,by simpa using hP,hD,?_⟩
  intro q hq hp
  rw [←integral_hillHierarchyNativeDensity m q hq hp]
  exact integral_evaluate_eq_of_total_derivative q q hq hq hp hp _ P R he

/-- The first member is the original physical quadratic mass. -/
theorem classicalHillHierarchyHamiltonian_zero (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1) :
    classicalHillHierarchyHamiltonian q 0 = classicalMKdVMass q := by
  rw [classicalHillHierarchyHamiltonian,hillRiccatiPolynomial,
    integral_scalarHillRiccati_two q q hq hq hp hp]
  simp only [evaluate_X,iteratedDeriv_zero,Bool.false_eq_true,↓reduceIte,classicalMKdVMass]
  norm_num

/-- The second member is exactly the printed KdV H1. -/
theorem classicalHillHierarchyHamiltonian_one (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1) :
    classicalHillHierarchyHamiltonian q 1 = classicalHamiltonian q := by
  rw [classicalHillHierarchyHamiltonian,hillRiccatiPolynomial,
    integral_scalarHillRiccati_four q q hq hq hp hp]
  have he : evaluate q q (X (false,0)) = q := by funext x; simp [evaluate]
  rw [he]
  ring

/-- The third member is exactly the printed KdV2 H2. -/
theorem classicalHillHierarchyHamiltonian_two (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1) :
    classicalHillHierarchyHamiltonian q 2 = classicalKdV2Hamiltonian q := by
  rw [classicalHillHierarchyHamiltonian,hillRiccatiPolynomial,
    integral_scalarHillRiccati_six q q hq hq hp hp]
  have he : evaluate q q (X (false,0)) = q := by funext x; simp [evaluate]
  rw [he]
  ring

end NLS.KdV
