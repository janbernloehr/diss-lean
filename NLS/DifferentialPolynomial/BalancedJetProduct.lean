import NLS.DifferentialPolynomial.PeriodicEvaluation

/-! # Balancing the leading pair of derivatives

Repeated integration by parts is recorded as an exact polynomial identity
modulo a total derivative, then transferred to periodic physical integrals.
-/
noncomputable section
open MvPolynomial Set MeasureTheory
open scoped ContDiff
namespace NLS.DifferentialPolynomial

/-- Transfer m derivatives between the two fields, retaining an explicit
polynomial whose derivative is the difference. -/
theorem exists_balanced_jet_product (j m n : ℕ) :
    ∃ r : Polynomial, X (false,j)*X (true,m+n) =
      C ((-1:ℂ)^m)*X (false,j+m)*X (true,n)+spatialDerivative r := by
  induction m generalizing j with
  | zero => exact ⟨0,by simp⟩
  | succ m ih =>
    obtain ⟨r,hr⟩ := ih (j+1)
    refine ⟨X (false,j)*X (true,m+n)-r,?_⟩
    have he : X (false,j)*X (true,m+1+n) =
        -(X (false,j+1)*X (true,m+n))+
          spatialDerivative (X (false,j)*X (true,m+n)) := by
      rw [Derivation.leibniz,spatialDerivative_X,spatialDerivative_X]
      simp only [nextJet,smul_eq_mul]
      rw [show m+1+n = m+n+1 by omega]
      ring
    rw [he,hr,map_sub,show j+1+m = j+(m+1) by omega]
    simp only [pow_succ,map_mul,map_neg,map_one]
    ring

/-- The leading derivative term has its usual balanced periodic integral. -/
theorem integral_balanced_derivatives (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (m : ℕ) :
    (∫ x in (0:ℝ)..1, a x*iteratedDeriv (2*m) b x) =
      (-1:ℂ)^m * ∫ x in (0:ℝ)..1, iteratedDeriv m a x*iteratedDeriv m b x := by
  obtain ⟨r,hr⟩ := exists_balanced_jet_product 0 m m
  have he := integral_evaluate_eq_of_total_derivative a b ha hb hpa hpb _ _ r hr
  simp only [evaluate_mul,evaluate_C,evaluate_X,Pi.mul_apply,Nat.zero_add,
    iteratedDeriv_zero,Bool.false_eq_true,↓reduceIte] at he
  simpa only [two_mul,intervalIntegral.integral_const_mul,mul_assoc] using he

end NLS.DifferentialPolynomial
