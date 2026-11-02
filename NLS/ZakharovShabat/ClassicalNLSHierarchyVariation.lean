import NLS.DifferentialPolynomial.SmoothVariation
import NLS.ZakharovShabat.NLSRiccatiPolynomials

/-! # All-order physical gradients of the NLS Hamiltonians

The normalization is the existing Riccati hierarchy, including its powers of
`-i`. The gradient is certified by the actual complex first variation, on
arbitrary smooth complex periodic fields at every Hamiltonian order.
-/
noncomputable section
open MvPolynomial Complex MeasureTheory NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Differential-polynomial density of the already defined physical hierarchy. -/
def nlsHamiltonianPolynomial : ℕ → DifferentialPolynomial.Polynomial
  | 0 => 0
  | n+1 => C ((-I)^(n+2)) * X (false,0) * nlsRiccatiPolynomial n

theorem integral_evaluate_nlsHamiltonianPolynomial (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (k : ℕ) :
    (∫ x in (0 : ℝ)..1, evaluate a b (nlsHamiltonianPolynomial k) x) =
      classicalNLSHamiltonian a b k := by
  cases k with
  | zero => simp [nlsHamiltonianPolynomial, evaluate, classicalNLSHamiltonian]
  | succ n =>
    simp only [nlsHamiltonianPolynomial, evaluate_mul, evaluate_C, evaluate_X,
      evaluate_nlsRiccatiPolynomial a b ha hb, Pi.mul_apply,
      iteratedDeriv_zero, Bool.false_eq_true, ↓reduceIte, classicalNLSHamiltonian]
    simp_rw [mul_assoc]
    exact intervalIntegral.integral_const_mul _ _

/-- The two physical variational-gradient components, at any hierarchy order. -/
def classicalNLSHierarchyGradient (a b : ℝ → ℂ) (k : ℕ) (x : ℝ) : ℂ × ℂ :=
  (evaluate a b (eulerDerivative false (nlsHamiltonianPolynomial k)) x,
    evaluate a b (eulerDerivative true (nlsHamiltonianPolynomial k)) x)

/-- This is a derivative of the existing Hamiltonian itself, rather than a
formal definition of its first variation. -/
theorem hasDerivAt_classicalNLSHamiltonian (a b h l : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hh : ContDiff ℝ ∞ h) (hl : ContDiff ℝ ∞ l)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) (hpl : Function.Periodic l 1) (k : ℕ) :
    HasDerivAt (fun z : ℂ =>
      classicalNLSHamiltonian (fun t => a t + z*h t) (fun t => b t + z*l t) k)
      (∫ x in (0 : ℝ)..1, h x * (classicalNLSHierarchyGradient a b k x).1 +
        l x * (classicalNLSHierarchyGradient a b k x).2) 0 := by
  have he (z : ℂ) := integral_evaluate_nlsHamiltonianPolynomial
    (fun t => a t + z*h t) (fun t => b t + z*l t)
    (ha.add (contDiff_const.mul hh)) (hb.add (contDiff_const.mul hl)) k
  simpa only [he, classicalNLSHierarchyGradient] using
    hasDerivAt_integral_evaluate_euler a b h l ha hb hh hl hpa hpb hph hpl
      (nlsHamiltonianPolynomial k)

theorem contDiff_classicalNLSHierarchyGradient (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (k : ℕ) :
    ContDiff ℝ ∞ (classicalNLSHierarchyGradient a b k) :=
  (contDiff_evaluate a b ha hb _).prodMk (contDiff_evaluate a b ha hb _)

theorem periodic_classicalNLSHierarchyGradient (a b : ℝ → ℂ)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (k : ℕ) :
    Function.Periodic (classicalNLSHierarchyGradient a b k) 1 := by
  intro x
  exact Prod.ext (periodic_evaluate a b 1 hpa hpb _ x)
    (periodic_evaluate a b 1 hpa hpb _ x)

end NLS.ZakharovShabat
