import NLS.MKdV.MiuraGapIdentification
import NLS.Articles.MKdVNLSHierarchies.SpectralIdentification

/-! # Lemma 3: the exact indexed endpoint and gap comparison

Full real H¹ profiles, the original NLS endpoints and independently
constructed physical Hill labels are used. These statements prove the
fixed-index, square-image and collapsed-gap parts of Lemma 3. Geometric
eigenspace multiplicity is a separate obligation.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem lemma3_ground_endpoints (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    (miuraHillLabels a ha 0 : ℂ) = (miuraNLSRight a 0)^2 ∧
    (miuraHillLabels a ha 0 : ℂ) = (miuraNLSLeft a 0)^2 :=
  miuraHillLabels_ground_complex a ha

theorem lemma3_indexed_endpoints (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    (miuraHillLabels a ha (2*n-1) : ℂ) = (miuraNLSLeft a n)^2 ∧
    (miuraHillLabels a ha (2*n) : ℂ) = (miuraNLSRight a n)^2 :=
  miuraHillLabels_endpoints_complex a ha n hn

theorem lemma3_gap_square_image (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    (fun x : ℝ => x^2) '' Icc (miuraNLSLeft a n).re (miuraNLSRight a n).re =
      Icc (miuraHillLabels a ha (2*n-1)) (miuraHillLabels a ha (2*n)) :=
  miuraHillGap_square_image a ha n hn

theorem lemma3_gap_collapsed_iff (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    miuraHillLabels a ha (2*n-1) = miuraHillLabels a ha (2*n) ↔
      miuraNLSLeft a n = miuraNLSRight a n :=
  miuraHillGap_collapsed_iff a ha n hn

end NLS.Articles.MKdVNLSHierarchies
