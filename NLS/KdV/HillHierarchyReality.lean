import NLS.KdV.HillRiccatiHierarchy
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Every independent physical source Hamiltonian is real on smooth real potentials. -/

noncomputable section
set_option autoImplicit false
open Complex MeasureTheory NLS.DifferentialPolynomial
open scoped ContDiff ComplexConjugate
namespace NLS.KdV

theorem conj_evaluate_hillRiccatiPolynomial (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q)
    (hr : ∀ x, (q x).im = 0) (n : ℕ) (x : ℝ) :
    conj (evaluate q 0 (hillRiccatiPolynomial n) x) =
      evaluate q 0 (hillRiccatiPolynomial n) x := by
  have hconj (x : ℝ) : conj (q x) = q x := by apply Complex.ext <;> simp [hr x]
  have hd (f : ℝ → ℂ) (hc : ∀ y, conj (f y) = f y) (y : ℝ) :
      conj (deriv f y) = deriv f y := by
    have he : (fun u => conj (f u)) = f := funext hc
    have hh := deriv.star (f := f) (x := y)
    change deriv (fun u => conj (f u)) y = conj (deriv f y) at hh
    rw [he] at hh
    exact hh.symm
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa using hconj x
    · simpa [iteratedDeriv_one] using congrArg Neg.neg (hd q hconj x)
    · rw [hillRiccatiPolynomial_recurrence]
      simp only [sub_eq_add_neg, evaluate_add, evaluate_neg,
        evaluate_spatialDerivative q 0 hq contDiff_const, Pi.add_apply, Pi.neg_apply,
        map_add, map_neg]
      rw [hd _ (ih (n+1) (by omega)) x]
      congr 2
      simp only [evaluate, map_sum, map_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have he := Finset.mem_antidiagonal.mp hij
      exact congrArg₂ (fun a b : ℂ => a*b)
        (ih ij.1 (by omega) x) (ih ij.2 (by omega) x)

theorem conj_classicalKdVHierarchyHamiltonian_of_real (q : ℝ → ℂ)
    (hq : ContDiff ℝ ∞ q) (hr : ∀ x, (q x).im = 0) (m : ℕ) :
    conj (classicalKdVHierarchyHamiltonian q m) = classicalKdVHierarchyHamiltonian q m := by
  rw [classicalKdVHierarchyHamiltonian, map_mul, ← intervalIntegral.intervalIntegral_conj]
  simp only [map_div₀, map_pow, map_neg, map_one, map_ofNat]
  rw [show (fun x => conj (evaluate q 0 (hillRiccatiPolynomial (2*m+2)) x)) =
      evaluate q 0 (hillRiccatiPolynomial (2*m+2)) from
    funext (conj_evaluate_hillRiccatiPolynomial q hq hr (2*m+2))]

end NLS.KdV
