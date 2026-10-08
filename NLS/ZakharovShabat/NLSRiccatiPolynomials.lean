import NLS.DifferentialPolynomial.JetDegrees
import NLS.ZakharovShabat.NLSRiccatiHierarchy

/-! # Canonical differential polynomials for the Riccati hierarchy

These are actual multivariate polynomials in the jets of the two fields.
Their evaluation is the existing classical differential recurrence.
-/
noncomputable section
open MvPolynomial NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.ZakharovShabat

def nlsRiccatiPolynomial : ℕ → DifferentialPolynomial.Polynomial
  | 0 => -X (true,0)
  | 1 => -X (true,1)
  | n+2 => spatialDerivative (nlsRiccatiPolynomial (n+1)) + X (false,0) *
      ∑ ij ∈ (Finset.antidiagonal n).attach,
        nlsRiccatiPolynomial ij.val.1 * nlsRiccatiPolynomial ij.val.2
termination_by n => n
decreasing_by
  all_goals first | omega | (have h := Finset.mem_antidiagonal.mp ij.property; omega)

@[simp] theorem nlsRiccatiPolynomial_zero : nlsRiccatiPolynomial 0 = -X (true,0) := by
  rw [nlsRiccatiPolynomial]

@[simp] theorem nlsRiccatiPolynomial_one : nlsRiccatiPolynomial 1 = -X (true,1) := by
  rw [nlsRiccatiPolynomial]

theorem nlsRiccatiPolynomial_succ_succ (n : ℕ) :
    nlsRiccatiPolynomial (n+2) = spatialDerivative (nlsRiccatiPolynomial (n+1)) + X (false,0) *
      ∑ ij ∈ (Finset.antidiagonal n).attach,
        nlsRiccatiPolynomial ij.val.1 * nlsRiccatiPolynomial ij.val.2 := by
  rw [nlsRiccatiPolynomial]

/-- A computation-friendly recurrence over ordinary antidiagonal pairs. -/
theorem nlsRiccatiPolynomial_recurrence (n : ℕ) :
    nlsRiccatiPolynomial (n+2) = spatialDerivative (nlsRiccatiPolynomial (n+1)) + X (false,0) *
      ∑ ij ∈ Finset.antidiagonal n, nlsRiccatiPolynomial ij.1*nlsRiccatiPolynomial ij.2 := by
  rw [nlsRiccatiPolynomial_succ_succ]
  exact congrArg (fun p : DifferentialPolynomial.Polynomial =>
    spatialDerivative (nlsRiccatiPolynomial (n+1))+X (false,0)*p)
    (Finset.sum_attach _ (fun ij : ℕ × ℕ => nlsRiccatiPolynomial ij.1*nlsRiccatiPolynomial ij.2))

/-- Polynomial evaluation exactly recovers the physical differential density. -/
theorem evaluate_nlsRiccatiPolynomial (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (n : ℕ) :
    evaluate a b (nlsRiccatiPolynomial n) = nlsRiccatiDensity a b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp
    · simp [iteratedDeriv_succ]
    · rw [nlsRiccatiPolynomial_succ_succ,nlsRiccatiDensity]
      rw [evaluate_add,evaluate_mul,evaluate_X,evaluate_spatialDerivative a b ha hb,
        ih (n+1) (by omega)]
      congr 1
      funext x
      simp only [evaluate,MvPolynomial.eval_sum,MvPolynomial.eval_mul,Pi.mul_apply,
        Finset.sum_apply,iteratedDeriv_zero,Bool.false_eq_true,↓reduceIte]
      congr 1
      apply Finset.sum_congr rfl
      intro ij _
      have hij := Finset.mem_antidiagonal.mp ij.property
      exact congrArg₂ (fun f g : ℝ → ℂ => f x*g x)
        (ih ij.val.1 (by omega)) (ih ij.val.2 (by omega))

/-- Total degree n+1 counts each field and each spatial derivative once. -/
theorem nlsRiccatiPolynomial_totalWeight (n : ℕ) :
    (nlsRiccatiPolynomial n).IsWeightedHomogeneous totalWeight (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa [totalWeight] using (isWeightedHomogeneous_X (R := ℂ) totalWeight (true,0)).neg
    · simpa [totalWeight] using (isWeightedHomogeneous_X (R := ℂ) totalWeight (true,1)).neg
    · rw [nlsRiccatiPolynomial_succ_succ]
      apply IsWeightedHomogeneous.add
      · convert totalWeight_spatialDerivative (ih (n+1) (by omega)) using 1
        push_cast
        ring
      · have hsum : (∑ ij ∈ (Finset.antidiagonal n).attach,
            nlsRiccatiPolynomial ij.val.1*nlsRiccatiPolynomial ij.val.2).IsWeightedHomogeneous
            totalWeight (n+2) := by
          apply IsWeightedHomogeneous.sum
          intro ij _
          have hij := Finset.mem_antidiagonal.mp ij.property
          convert (ih ij.val.1 (by omega)).mul (ih ij.val.2 (by omega)) using 1
          omega
        convert (isWeightedHomogeneous_X (R := ℂ) totalWeight (false,0)).mul hsum using 1
        simp only [totalWeight,Nat.cast_add]
        ring

/-- Each monomial has one more second-field factor than first-field factor. -/
theorem nlsRiccatiPolynomial_fieldCharge (n : ℕ) :
    (nlsRiccatiPolynomial n).IsWeightedHomogeneous fieldCharge 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa [fieldCharge] using (isWeightedHomogeneous_X (R := ℂ) fieldCharge (true,0)).neg
    · simpa [fieldCharge] using (isWeightedHomogeneous_X (R := ℂ) fieldCharge (true,1)).neg
    · rw [nlsRiccatiPolynomial_succ_succ]
      apply (fieldCharge_spatialDerivative (ih (n+1) (by omega))).add
      have hsum : (∑ ij ∈ (Finset.antidiagonal n).attach,
          nlsRiccatiPolynomial ij.val.1*nlsRiccatiPolynomial ij.val.2).IsWeightedHomogeneous
          fieldCharge (1+1) := by
        apply IsWeightedHomogeneous.sum
        intro ij _
        have hij := Finset.mem_antidiagonal.mp ij.property
        exact (ih ij.val.1 (by omega)).mul (ih ij.val.2 (by omega))
      simpa [fieldCharge] using (isWeightedHomogeneous_X (R := ℂ) fieldCharge (false,0)).mul hsum

/-- The total number of derivatives in each density monomial is at most n. -/
theorem nlsRiccatiPolynomial_derivativeOrder (n : ℕ) :
    DerivativeOrderLE (nlsRiccatiPolynomial n) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa using (DerivativeOrderLE.X (true,0)).neg
    · simpa using (DerivativeOrderLE.X (true,1)).neg
    · rw [nlsRiccatiPolynomial_succ_succ]
      apply DerivativeOrderLE.add
      · convert (ih (n+1) (by omega)).spatialDerivative using 1
        push_cast
        ring
      · have hsum : DerivativeOrderLE (∑ ij ∈ (Finset.antidiagonal n).attach,
            nlsRiccatiPolynomial ij.val.1*nlsRiccatiPolynomial ij.val.2) n := by
          apply DerivativeOrderLE.sum
          intro ij _
          have hij := Finset.mem_antidiagonal.mp ij.property
          convert (ih ij.val.1 (by omega)).mul (ih ij.val.2 (by omega)) using 1
          omega
        apply ((DerivativeOrderLE.X (false,0)).mul hsum).mono
        push_cast
        omega

end NLS.ZakharovShabat
