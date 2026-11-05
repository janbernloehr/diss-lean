import NLS.MKdV.MiuraSpectralActionContours
import NLS.Articles.MKdVNLSHierarchies.ActionIdentification

/-! # Theorem 4(i) and the real integer-level identity of Lemma 7

The mKdV actions are the actual inverse-energy-weighted contours of the
independently constructed physical Hill primitive. Their isolating loops,
windings, integer-level change of variables, contour-choice independence
and positive real-gap representations are proved in the shared library.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem lemma7_integer_levels_real_H1 (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    2*miuraMKdVActionLevel a ha n k = sourceLaurentActionContour (by simp) (by norm_num)
      (realDiagonalH1Source a ha) (2*k-2) ((miuraActionContourFamily a ha).frequencyContour n) :=
  miuraMKdVActionLevel_eq_NLSLaurent a ha n hn k

theorem theorem4_i_positive_actions (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    miuraNLSAction a n = 0 ↔ miuraMKdVAction a ha n = 0 :=
  (miuraMKdVAction_nonnegative_and_zero_iff a ha n hn).2.2.symm

/-- All three clauses on every original real period-one H¹ input,
including zero mean, collapsed gaps and arbitrary positive gap indices. -/
theorem theorem4_i (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) :
    (miuraNLSAction a 0 = 0 ↔ a.val 0 = 0) ∧
      (∀ n : ℕ, 1 ≤ n → (miuraNLSAction a n = 0 ↔ miuraMKdVAction a ha n = 0)) ∧
      (∀ n : ℤ, miuraNLSAction a (-n) = miuraNLSAction a n) :=
  ⟨theorem4_i_central_action_zero a ha,theorem4_i_positive_actions a ha,theorem4_i_action_reflection a ha⟩

end NLS.Articles.MKdVNLSHierarchies
