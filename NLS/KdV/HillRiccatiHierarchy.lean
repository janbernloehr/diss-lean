import NLS.DifferentialPolynomial.ScalarRiccatiLogarithm
import NLS.KdV.RiccatiEnergy
import NLS.ZakharovShabat.ClassicalNLSHamiltonians

/-! # The independent physical KdV hierarchy from the scalar Riccati recurrence

This is Appendix B, equation (19), of arXiv:1502.04550v1. The index zero
polynomial is s₁=q. Both recurrence signs and the factor (-1)^(m+1)/2
are fixed before any comparison with spectral coefficients. All odd
integrated densities vanish by explicit polynomial total derivatives.
-/

noncomputable section
set_option autoImplicit false
open MvPolynomial Complex MeasureTheory
open scoped ContDiff
open NLS.DifferentialPolynomial NLS.ZakharovShabat
namespace NLS.KdV

/-- The source scalar recurrence, indexed with `0` for its `s₁=q`. -/
def hillRiccatiPolynomial (n : ℕ) : DifferentialPolynomial.Polynomial :=
  differentialRiccatiSequence (-spatialDerivative) (-1) (-X (false,0)) n

@[simp] theorem hillRiccatiPolynomial_zero : hillRiccatiPolynomial 0 = X (false,0) := by
  simp [hillRiccatiPolynomial]

@[simp] theorem hillRiccatiPolynomial_one : hillRiccatiPolynomial 1 = -X (false,1) := by
  simp [hillRiccatiPolynomial, Derivation.neg_apply, nextJet]

theorem hillRiccatiPolynomial_recurrence (n : ℕ) :
    hillRiccatiPolynomial (n+2) = -spatialDerivative (hillRiccatiPolynomial (n+1)) -
      ∑ ij ∈ Finset.antidiagonal n,
        hillRiccatiPolynomial ij.1 * hillRiccatiPolynomial ij.2 := by
  simpa only [hillRiccatiPolynomial, Derivation.neg_apply, neg_one_mul, sub_eq_add_neg] using
    differentialRiccatiSequence_recurrence (-spatialDerivative) (-1) (-X (false,0)) n

/-- Scalar KdV grading: q has weight two and each derivative adds one. -/
def hillJetWeight (v : Jet) : ℤ := (v.2 : ℤ)+2

/-- Every density has the source's exact scalar differential grading. -/
theorem hillRiccatiPolynomial_homogeneous (n : ℕ) :
    (hillRiccatiPolynomial n).IsWeightedHomogeneous hillJetWeight ((n : ℤ)+2) := by
  have hw (v : Jet) : hillJetWeight (nextJet v) = hillJetWeight v+1 := by
    simp only [hillJetWeight, nextJet, Nat.cast_add, Nat.cast_one]
    omega
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa [hillJetWeight] using
        (isWeightedHomogeneous_X (R := ℂ) hillJetWeight (false,0))
    · simpa [hillJetWeight] using
        (isWeightedHomogeneous_X (R := ℂ) hillJetWeight (false,1)).neg
    · rw [hillRiccatiPolynomial_recurrence, sub_eq_add_neg]
      apply IsWeightedHomogeneous.add
      · convert! (homogeneous_spatialDerivative hillJetWeight 1 _ hw
          (ih (n+1) (by omega))).neg using 1
      · apply IsWeightedHomogeneous.neg
        apply IsWeightedHomogeneous.sum
        intro ij hij
        have he := Finset.mem_antidiagonal.mp hij
        convert! (ih ij.1 (by omega)).mul (ih ij.2 (by omega)) using 1
        omega

/-- The total number of spatial derivatives in each density monomial is at most n. -/
theorem hillRiccatiPolynomial_derivativeOrder (n : ℕ) :
    DerivativeOrderLE (hillRiccatiPolynomial n) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa using DerivativeOrderLE.X (false,0)
    · simpa using (DerivativeOrderLE.X (false,1)).neg
    · rw [hillRiccatiPolynomial_recurrence, sub_eq_add_neg]
      apply DerivativeOrderLE.add
      · convert (ih (n+1) (by omega)).spatialDerivative.neg using 1
        push_cast
        omega
      · apply DerivativeOrderLE.neg
        apply DerivativeOrderLE.mono (d := (n : ℤ))
        · apply DerivativeOrderLE.sum
          intro ij hij
          have he := Finset.mem_antidiagonal.mp hij
          convert (ih ij.1 (by omega)).mul (ih ij.2 (by omega)) using 1
          exact_mod_cast he.symm
        · omega

/-- Appendix B, equation (19), defined from scalar differential polynomials. -/
def classicalKdVHierarchyHamiltonian (q : ℝ → ℂ) (m : ℕ) : ℂ :=
  (-1 : ℂ)^(m+1) / 2 *
    ∫ x in (0 : ℝ)..1, evaluate q 0 (hillRiccatiPolynomial (2*m+2)) x

theorem evaluate_positive_hillRiccatiPolynomial (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (n : ℕ) :
    evaluate q 0 (differentialRiccatiSequence spatialDerivative (-1) (-X (false,0)) n) =
      nlsRiccatiDensity (fun _ => -1) (-q) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp
    · simp [nextJet, iteratedDeriv_one]
      funext x
      simp
    · rw [differentialRiccatiSequence_recurrence, nlsRiccatiDensity_succ_succ,
        evaluate_add, evaluate_mul, evaluate_spatialDerivative q 0 hq contDiff_const,
        ih (n+1) (by omega)]
      congr 1
      funext x
      simp only [Pi.mul_apply, evaluate, MvPolynomial.eval_neg, map_one,
        MvPolynomial.eval_sum, MvPolynomial.eval_mul, neg_one_mul,
        Finset.sum_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro ij hij
      have he := Finset.mem_antidiagonal.mp hij
      exact congrArg₂ (fun f g : ℝ → ℂ => f x*g x)
        (ih ij.1 (by omega)) (ih ij.2 (by omega))

theorem evaluate_hillRiccatiPolynomial (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (n : ℕ) :
    evaluate q 0 (hillRiccatiPolynomial n) =
      fun x => (-1 : ℂ)^n * nlsRiccatiDensity (fun _ => -1) (-q) n x := by
  rw [hillRiccatiPolynomial, differentialRiccatiSequence_neg_derivation]
  funext x
  simp only [evaluate, MvPolynomial.eval_mul, map_pow, map_neg, map_one]
  exact congrArg (fun f : ℝ → ℂ => (-1 : ℂ)^n * f x)
    (evaluate_positive_hillRiccatiPolynomial q hq n)

theorem evaluate_hillRiccatiPolynomial_even (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (m : ℕ) :
    evaluate q 0 (hillRiccatiPolynomial (2*m+2)) =
      nlsRiccatiDensity (fun _ => -1) (-q) (2*m+2) := by
  rw [evaluate_hillRiccatiPolynomial q hq]
  have he : (-1 : ℂ)^(2*m+2) = 1 := by
    rw [show 2*m+2 = 2*(m+1) by omega, pow_mul]
    norm_num
  simp only [he, one_mul]

theorem classicalNLSHamiltonian_const_upper_odd (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (m : ℕ) :
    classicalNLSHamiltonian (fun _ => -1) (-q) (2*m+3) =
      2 * classicalKdVHierarchyHamiltonian q m := by
  rw [show 2*m+3 = (2*m+2)+1 by omega, classicalNLSHamiltonian]
  simp only [neg_one_mul, intervalIntegral.integral_neg]
  rw [classicalKdVHierarchyHamiltonian, evaluate_hillRiccatiPolynomial_even q hq]
  have hp : (-I : ℂ)^(2*m+2+2) = (-1 : ℂ)^(m+2) := by
    rw [show 2*m+2+2 = 2*(m+2) by omega, pow_mul]
    norm_num [neg_sq, I_sq]
  rw [hp]
  ring

theorem classicalKdVHierarchyHamiltonian_zero (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) :
    classicalKdVHierarchyHamiltonian q 0 = classicalQuadraticInvariant q := by
  have he := classicalNLSHamiltonian_const_upper_odd q hq 0
  rw [show 2*0+3 = 3 by omega, classicalNLSHamiltonian_const_upper_three q hq hp] at he
  linear_combination -he / 2

theorem classicalKdVHierarchyHamiltonian_one (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) :
    classicalKdVHierarchyHamiltonian q 1 = classicalHamiltonian q := by
  have he := classicalNLSHamiltonian_const_upper_odd q hq 1
  rw [show 2*1+3 = 5 by omega, classicalNLSHamiltonian_const_upper_five q hq hp] at he
  linear_combination -he / 2

/-- A finite differential polynomial whose spatial derivative is the odd density. -/
def hillRiccatiOddPrimitive (m : ℕ) : DifferentialPolynomial.Polynomial :=
  C (-1/2 : ℂ) * logarithmicPrimitiveCoefficient (K := ℂ)
    (scalarRiccatiLogInput spatialDerivative (X (false,0))) (2*m+1)

theorem spatialDerivative_hillRiccatiOddPrimitive (m : ℕ) :
    spatialDerivative (hillRiccatiOddPrimitive m) = hillRiccatiPolynomial (2*m+1) := by
  simp only [hillRiccatiOddPrimitive, Derivation.leibniz, smul_eq_mul,
    MvPolynomial.derivation_C, mul_zero, add_zero]
  rw [derivation_scalarRiccati_log_odd]
  change C (-1/2 : ℂ) * (-2 * hillRiccatiPolynomial (2*m+1)) = _
  have hc : C (-1/2 : ℂ) * (-2 : DifferentialPolynomial.Polynomial) = 1 := by
    have h2 : (-2 : DifferentialPolynomial.Polynomial) = C (-2 : ℂ) := by
      rw [show (-2 : ℂ) = -(1+1) by norm_num, map_neg, map_add, map_one]
      ring
    rw [h2, ← map_mul]
    norm_num
  rw [← mul_assoc, hc, one_mul]

theorem integral_hillRiccatiPolynomial_odd (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) (m : ℕ) :
    (∫ x in (0 : ℝ)..1, evaluate q 0 (hillRiccatiPolynomial (2*m+1)) x) = 0 := by
  rw [← spatialDerivative_hillRiccatiOddPrimitive]
  exact integral_evaluate_spatialDerivative q 0 hq contDiff_const hp (fun _ => rfl) _

theorem integral_nlsRiccatiDensity_const_upper_odd (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) (m : ℕ) :
    (∫ x in (0 : ℝ)..1, nlsRiccatiDensity (fun _ => -1) (-q) (2*m+1) x) = 0 := by
  have he : evaluate q 0 (hillRiccatiPolynomial (2*m+1)) =
      -nlsRiccatiDensity (fun _ => -1) (-q) (2*m+1) := by
    rw [evaluate_hillRiccatiPolynomial q hq]
    have hpow : (-1 : ℂ)^(2*m+1) = -1 := by
      rw [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
    funext x
    simp only [hpow, neg_one_mul, Pi.neg_apply]
  have hi := integral_hillRiccatiPolynomial_odd q hq hp m
  rw [he] at hi
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at hi
  exact neg_eq_zero.mp hi

/-- Every even specialized Hamiltonian vanishes on smooth periodic potentials. -/
theorem classicalNLSHamiltonian_const_upper_even (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hp : Function.Periodic q 1) (m : ℕ) :
    classicalNLSHamiltonian (fun _ => -1) (-q) (2*m+2) = 0 := by
  rw [show 2*m+2 = (2*m+1)+1 by omega, classicalNLSHamiltonian]
  simp only [neg_one_mul, intervalIntegral.integral_neg,
    integral_nlsRiccatiDensity_const_upper_odd q hq hp, neg_zero, mul_zero]

end NLS.KdV
