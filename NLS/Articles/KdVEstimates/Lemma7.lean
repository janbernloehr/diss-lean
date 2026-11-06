import NLS.KdV.HillHamiltonianMonomials

/-! The polynomial assertion of Lemma 7, including the absent constant term.
The integer grading doubles the paper's grading: q has weight two and each
spatial derivative adds one. Thus degree m+2 becomes 2*m+4. -/

noncomputable section
set_option autoImplicit false
open NLS.KdV NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.Articles.KdVEstimates

theorem lemma7 (m : ℕ) (hm : 1 ≤ m) :
    ∃ p : DifferentialPolynomial.Polynomial, JetOrderLE p (m-1) ∧
      p.IsWeightedHomogeneous hillJetWeight (2*(m : ℤ)+4) ∧
      MvPolynomial.coeff 0 p = 0 ∧
      ∀ q : ℝ → ℂ, ContDiff ℝ ∞ q → Function.Periodic q 1 →
        classicalKdVHierarchyHamiltonian q m = (1/2 : ℂ)*∫ x in (0 : ℝ)..1,
          (iteratedDeriv m q x)^2+evaluate q 0 p x := by
  obtain ⟨p,ho,hw,hformula⟩ :=
    exists_classicalKdVHierarchyHamiltonian_reduced_polynomial m hm
  refine ⟨p,ho,hw,?_,hformula⟩
  exact hw.coeff_eq_zero 0 (by simp; omega)

/-- The exact monomial constraint (14), without introducing half-integer indices. -/
theorem lemma7_monomial_constraint (m : ℕ) (hm : 1 ≤ m)
    (d : Monomial) (hd : d ∈ (hillReducedPolynomial m hm).support) :
    (∑ k ∈ Finset.range m, (k+2)*jetMultiplicity d k) = 2*m+4 :=
  hillReducedPolynomial_multiplicity_weight m hm d hd

end NLS.Articles.KdVEstimates
