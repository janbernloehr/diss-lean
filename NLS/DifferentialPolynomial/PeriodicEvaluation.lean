import NLS.DifferentialPolynomial.IntegrationByPartsReduction
import NLS.ZakharovShabat.ClassicalNLSHamiltonians

/-! # Periodic integrals of differential polynomials

Total spatial derivatives have zero integral over a period. Consequently the
explicit polynomial reduction preserves the actual physical integral.
-/
noncomputable section
open MvPolynomial Set MeasureTheory
open scoped ContDiff
namespace NLS.DifferentialPolynomial

/-- Smooth-field evaluation of any differential polynomial is continuous. -/
theorem continuous_evaluate (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (p : Polynomial) : Continuous (evaluate a b p) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_evaluate a b ha hb p x).continuousAt)

/-- Every jet retains the original period. -/
theorem periodic_iteratedDeriv (f : ℝ → ℂ) (T : ℝ) (hf : Function.Periodic f T) (n : ℕ) :
    Function.Periodic (iteratedDeriv n f) T := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ZakharovShabat.periodic_deriv_of_periodic _ T ih

/-- Polynomial evaluation retains the common period of its two fields. -/
theorem periodic_evaluate (a b : ℝ → ℂ) (T : ℝ)
    (ha : Function.Periodic a T) (hb : Function.Periodic b T) (p : Polynomial) :
    Function.Periodic (evaluate a b p) T := by
  intro x
  unfold evaluate
  apply congrArg (fun f : Jet → ℂ => MvPolynomial.eval f p)
  funext v
  exact periodic_iteratedDeriv _ T (by split <;> assumption) v.2 x

/-- A polynomial total derivative integrates to zero on smooth periodic fields. -/
theorem integral_evaluate_spatialDerivative (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (p : Polynomial) :
    (∫ x in (0:ℝ)..1, evaluate a b (spatialDerivative p) x) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_evaluate a b ha hb p x)
    ((continuous_evaluate a b ha hb (spatialDerivative p)).intervalIntegrable 0 1)]
  have he : evaluate a b p 1 = evaluate a b p 0 := by
    simpa only [zero_add] using periodic_evaluate a b 1 hpa hpb p 0
  rw [he,sub_self]

/-- The polynomial integration-by-parts identity preserves the physical integral. -/
theorem integral_evaluate_eq_of_total_derivative (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (p q r : Polynomial) (h : p = q+spatialDerivative r) :
    (∫ x in (0:ℝ)..1, evaluate a b p x) = ∫ x in (0:ℝ)..1, evaluate a b q x := by
  rw [h,evaluate_add]
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_add
    ((continuous_evaluate a b ha hb q).intervalIntegrable 0 1)
    ((continuous_evaluate a b ha hb (spatialDerivative r)).intervalIntegrable 0 1),
    integral_evaluate_spatialDerivative a b ha hb hpa hpb,add_zero]

/-- One reduced polynomial works for every smooth periodic pair of fields. -/
theorem exists_periodic_integral_jet_reduction (m : ℕ) (hm : 1 ≤ m)
    (p : Polynomial) (d c : ℤ)
    (hw : p.IsWeightedHomogeneous totalWeight d) (hc : p.IsWeightedHomogeneous fieldCharge c)
    (hd : DerivativeOrderLE p (2*(m:ℤ)-2)) :
    ∃ q : Polynomial, JetOrderLE q (m-1) ∧ q.IsWeightedHomogeneous totalWeight d ∧
      q.IsWeightedHomogeneous fieldCharge c ∧ DerivativeOrderLE q (2*(m:ℤ)-2) ∧
      ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
        Function.Periodic a 1 → Function.Periodic b 1 →
        (∫ x in (0:ℝ)..1, evaluate a b p x) = ∫ x in (0:ℝ)..1, evaluate a b q x := by
  obtain ⟨q,r,he,hq,hwq,hcq,hdq⟩ := exists_graded_jet_reduction m hm p d c hw hc hd
  exact ⟨q,hq,hwq,hcq,hdq,fun a b ha hb hpa hpb =>
    integral_evaluate_eq_of_total_derivative a b ha hb hpa hpb p q r he⟩

end NLS.DifferentialPolynomial
