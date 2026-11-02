import NLS.MKdV.MiuraActionLevelExtension
import NLS.Articles.MKdVNLSHierarchies.SpectralActionIdentification

/-! # Complete Lemma 7: real contour identity and ambient L² analyticity

One open complex L² source neighborhood contains the entire real diagonal
and supports every positive index and every integer level. The extension
is the actual Laurent-weighted NLS contour, agrees with the previously
constructed positive levels on their complex overlaps, and restricts to
twice the independently defined physical mKdV contour action.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem lemma7_analytic_extension :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ realDiagonalSourceLocus 2 ⊆ U ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ k : ℤ,
        AnalyticOnNhd ℂ (sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2)) U ∧
          ∀ (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))),
            sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2)
              (sobolevSourceInclusion (a,a)) = 2*miuraMKdVActionLevel a ha n k :=
  exists_miuraActionLevel_analytic_extension

/-- Lemma 7 with its original quantifiers and its final ambient analytic
extension clause, retaining the actual real NLS and Hill contours. -/
theorem lemma7 :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ realDiagonalSourceLocus 2 ⊆ U ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ k : ℤ,
        AnalyticOnNhd ℂ (sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2)) U ∧
          ∀ (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))),
            (sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2)
              (sobolevSourceInclusion (a,a)) = sourceLaurentActionContour (by simp) (by norm_num)
                (realDiagonalH1Source a ha) (2*k-2) ((miuraActionContourFamily a ha).frequencyContour n)) ∧
            sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2)
              (sobolevSourceInclusion (a,a)) = 2*miuraMKdVActionLevel a ha n k := by
  obtain ⟨U,hU,hreal,h⟩ := lemma7_analytic_extension
  refine ⟨U,hU,hreal,?_⟩
  intro n hn k
  refine ⟨(h n hn k).1,?_⟩
  intro a ha
  have he := (h n hn k).2 a ha
  exact ⟨he.trans (lemma7_integer_levels_real_H1 a ha n hn k),he⟩

end NLS.Articles.MKdVNLSHierarchies
