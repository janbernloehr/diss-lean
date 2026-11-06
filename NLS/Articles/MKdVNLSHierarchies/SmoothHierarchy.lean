import NLS.MKdV.MiuraHierarchyFlowRestriction

/-! # All-order smooth clauses toward Theorem 1 and Proposition 6

The scalar hierarchy is independently constructed from the Hill Riccati
recurrence at u'+u². The sharp H^m extension and full identification with
the article's spectral mKdV hierarchy are not asserted by these interfaces.
-/
noncomputable section
open NLS.MKdV NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.Articles.MKdVNLSHierarchies

/-- Proposition 6's odd Hamiltonian identity on smooth complex periodic
fields for the independently specified scalar Hill / Miura hierarchy. -/
theorem proposition6_smooth_miura (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u 1) (m : ℕ) (hm : 1 ≤ m) :
    classicalNLSHamiltonian u u (2*m-1) = 2*classicalMiuraHillHamiltonian u m := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r+1 := ⟨m-1, by omega⟩
  simpa only [show 2*(r+1)-1 = 2*r+1 by omega] using
    classicalNLSHamiltonian_odd_diagonal_eq_miuraHill u hu hp r

/-- Both Theorem 1 clauses at all smooth complex periodic orders for the
independently specified scalar Hill / Miura hierarchy. -/
theorem theorem1_smooth_miura_hierarchy (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u 1) (m : ℕ) (hm : 1 ≤ m) :
    classicalNLSHamiltonian u u (2*m) = 0 ∧
      ∀ x, classicalNLSHierarchyVectorField u u (2*m) x =
        (classicalMiuraHillVectorField u m x, classicalMiuraHillVectorField u m x) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r+1 := ⟨m-1, by omega⟩
  rw [show 2*(r+1) = 2*r+2 by omega]
  exact ⟨classicalNLSHamiltonian_even_diagonal_eq_zero u hu hp r,
    classicalNLSHierarchyVectorField_even_diagonal u hu hp r⟩

end NLS.Articles.MKdVNLSHierarchies
