import NLS.KdV.HillRiccatiHierarchy

/-! # Exact linear and quadratic Riccati parts and the four-derivative gain in the cubic remainder. -/

noncomputable section
set_option autoImplicit false
open MvPolynomial NLS.DifferentialPolynomial
namespace NLS.KdV

def hillRiccatiLinear (n : ℕ) : DifferentialPolynomial.Polynomial :=
  C ((-1 : ℂ)^n) * X (false,n)

theorem spatialDerivative_hillRiccatiLinear (n : ℕ) :
    spatialDerivative (hillRiccatiLinear n) = -hillRiccatiLinear (n+1) := by
  simp [hillRiccatiLinear, Derivation.leibniz,
    spatialDerivative_X, nextJet, pow_succ]

theorem hillRiccatiLinear_derivativeOrder (n : ℕ) :
    DerivativeOrderLE (hillRiccatiLinear n) n := by
  have hc : DerivativeOrderLE (C ((-1 : ℂ)^n)) 0 :=
    Supported.monomial 0 _ (by simp)
  simpa [hillRiccatiLinear] using hc.mul (DerivativeOrderLE.X (false,n))

def hillRiccatiNonlinear (n : ℕ) : DifferentialPolynomial.Polynomial :=
  hillRiccatiPolynomial n-hillRiccatiLinear n

@[simp] theorem hillRiccatiNonlinear_zero : hillRiccatiNonlinear 0 = 0 := by
  simp [hillRiccatiNonlinear, hillRiccatiLinear]

@[simp] theorem hillRiccatiNonlinear_one : hillRiccatiNonlinear 1 = 0 := by
  simp [hillRiccatiNonlinear, hillRiccatiLinear]

theorem hillRiccatiNonlinear_recurrence (n : ℕ) :
    hillRiccatiNonlinear (n+2) = -spatialDerivative (hillRiccatiNonlinear (n+1)) -
      ∑ ij ∈ Finset.antidiagonal n,
        hillRiccatiPolynomial ij.1 * hillRiccatiPolynomial ij.2 := by
  simp only [hillRiccatiNonlinear, hillRiccatiPolynomial_recurrence,
    map_sub, spatialDerivative_hillRiccatiLinear]
  ring

theorem hillRiccatiNonlinear_derivativeOrder (n : ℕ) :
    DerivativeOrderLE (hillRiccatiNonlinear n) ((n : ℤ)-2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [hillRiccatiNonlinear_zero]
      exact DerivativeOrderLE.zero _
    · rw [hillRiccatiNonlinear_one]
      exact DerivativeOrderLE.zero _
    · rw [hillRiccatiNonlinear_recurrence, sub_eq_add_neg]
      apply DerivativeOrderLE.add
      · convert (ih (n+1) (by omega)).spatialDerivative.neg using 1
        push_cast
        ring
      · apply DerivativeOrderLE.neg
        apply DerivativeOrderLE.sum
        intro ij hij
        have he := Finset.mem_antidiagonal.mp hij
        convert (hillRiccatiPolynomial_derivativeOrder ij.1).mul
          (hillRiccatiPolynomial_derivativeOrder ij.2) using 1
        omega

/-- The exact degree-two part, independently specified by its linear forcing. -/
def hillRiccatiQuadratic : ℕ → DifferentialPolynomial.Polynomial
  | 0 => 0
  | 1 => 0
  | n+2 => -spatialDerivative (hillRiccatiQuadratic (n+1)) -
      ∑ ij ∈ Finset.antidiagonal n, hillRiccatiLinear ij.1 * hillRiccatiLinear ij.2

@[simp] theorem hillRiccatiQuadratic_zero : hillRiccatiQuadratic 0 = 0 := rfl
@[simp] theorem hillRiccatiQuadratic_one : hillRiccatiQuadratic 1 = 0 := rfl

theorem hillRiccatiQuadratic_recurrence (n : ℕ) :
    hillRiccatiQuadratic (n+2) = -spatialDerivative (hillRiccatiQuadratic (n+1)) -
      ∑ ij ∈ Finset.antidiagonal n, hillRiccatiLinear ij.1 * hillRiccatiLinear ij.2 := rfl

def hillRiccatiCubicRemainder (n : ℕ) : DifferentialPolynomial.Polynomial :=
  hillRiccatiNonlinear n-hillRiccatiQuadratic n

@[simp] theorem hillRiccatiCubicRemainder_zero : hillRiccatiCubicRemainder 0 = 0 := by
  simp [hillRiccatiCubicRemainder]

@[simp] theorem hillRiccatiCubicRemainder_one : hillRiccatiCubicRemainder 1 = 0 := by
  simp [hillRiccatiCubicRemainder]

theorem hillRiccatiCubicRemainder_recurrence (n : ℕ) :
    hillRiccatiCubicRemainder (n+2) =
      -spatialDerivative (hillRiccatiCubicRemainder (n+1)) -
        ∑ ij ∈ Finset.antidiagonal n,
          (hillRiccatiNonlinear ij.1 * hillRiccatiPolynomial ij.2 +
            hillRiccatiLinear ij.1 * hillRiccatiNonlinear ij.2) := by
  simp only [hillRiccatiCubicRemainder, hillRiccatiNonlinear_recurrence,
    hillRiccatiQuadratic_recurrence, map_sub]
  have he : (∑ ij ∈ Finset.antidiagonal n,
      (hillRiccatiNonlinear ij.1*hillRiccatiPolynomial ij.2+
        hillRiccatiLinear ij.1*hillRiccatiNonlinear ij.2)) =
      (∑ ij ∈ Finset.antidiagonal n, hillRiccatiPolynomial ij.1*hillRiccatiPolynomial ij.2) -
        ∑ ij ∈ Finset.antidiagonal n, hillRiccatiLinear ij.1*hillRiccatiLinear ij.2 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ij _
    simp only [hillRiccatiNonlinear]
    ring
  rw [he]
  ring

/-- Removing the exact linear and quadratic parts saves four total derivatives. -/
theorem hillRiccatiCubicRemainder_derivativeOrder (n : ℕ) :
    DerivativeOrderLE (hillRiccatiCubicRemainder n) ((n : ℤ)-4) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [hillRiccatiCubicRemainder_zero]
      exact DerivativeOrderLE.zero _
    · rw [hillRiccatiCubicRemainder_one]
      exact DerivativeOrderLE.zero _
    · rw [hillRiccatiCubicRemainder_recurrence, sub_eq_add_neg]
      apply DerivativeOrderLE.add
      · convert (ih (n+1) (by omega)).spatialDerivative.neg using 1
        push_cast
        ring
      · apply DerivativeOrderLE.neg
        apply DerivativeOrderLE.sum
        intro ij hij
        have he := Finset.mem_antidiagonal.mp hij
        apply DerivativeOrderLE.add
        · convert (hillRiccatiNonlinear_derivativeOrder ij.1).mul
            (hillRiccatiPolynomial_derivativeOrder ij.2) using 1
          omega
        · convert (hillRiccatiLinear_derivativeOrder ij.1).mul
            (hillRiccatiNonlinear_derivativeOrder ij.2) using 1
          omega

theorem hillRiccatiLinear_homogeneous (n : ℕ) :
    (hillRiccatiLinear n).IsWeightedHomogeneous hillJetWeight ((n : ℤ)+2) := by
  simpa [hillRiccatiLinear, hillJetWeight] using
    (isWeightedHomogeneous_X (R := ℂ) hillJetWeight (false,n)).C_mul ((-1 : ℂ)^n)

theorem hillRiccatiQuadratic_homogeneous (n : ℕ) :
    (hillRiccatiQuadratic n).IsWeightedHomogeneous hillJetWeight ((n : ℤ)+2) := by
  have hw (v : Jet) : hillJetWeight (nextJet v) = hillJetWeight v+1 := by
    simp only [hillJetWeight, nextJet, Nat.cast_add, Nat.cast_one]
    omega
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [hillRiccatiQuadratic_zero]
      exact isWeightedHomogeneous_zero _ _ _
    · rw [hillRiccatiQuadratic_one]
      exact isWeightedHomogeneous_zero _ _ _
    · rw [hillRiccatiQuadratic_recurrence, sub_eq_add_neg]
      apply IsWeightedHomogeneous.add
      · convert! (homogeneous_spatialDerivative hillJetWeight 1 _ hw
          (ih (n+1) (by omega))).neg using 1
      · apply IsWeightedHomogeneous.neg
        apply IsWeightedHomogeneous.sum
        intro ij hij
        have he := Finset.mem_antidiagonal.mp hij
        convert! (hillRiccatiLinear_homogeneous ij.1).mul
          (hillRiccatiLinear_homogeneous ij.2) using 1
        omega

theorem hillRiccatiCubicRemainder_homogeneous (n : ℕ) :
    (hillRiccatiCubicRemainder n).IsWeightedHomogeneous hillJetWeight ((n : ℤ)+2) := by
  simpa only [hillRiccatiCubicRemainder, hillRiccatiNonlinear, sub_eq_add_neg] using
    ((hillRiccatiPolynomial_homogeneous n).add (hillRiccatiLinear_homogeneous n).neg).add
      (hillRiccatiQuadratic_homogeneous n).neg

end NLS.KdV
