import NLS.MKdV.MiuraActionReflection
import NLS.Articles.MKdVNLSHierarchies.GapIdentification

/-! # The central and reflection clauses of Theorem 4(i)

These are the existing NLS contour actions on the literal diagonal H¹
source. The physical mean is the original zeroth Fourier coefficient.
The positive action/Hill gap-zero comparison is also proved. Comparison
with the article's contour-defined mKdV actions J_n remains separate.
-/
noncomputable section
open Complex NLS.MKdV NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- Equation (21), for every original complex H¹ profile, using the
independently constructed physical L² Hill monodromy. -/
theorem equation21_physical_mean_trace (a : ScalarDomain 2) :
    hillL2Discriminant (sobolevMiuraHillPotential a) 0 = 2*cosh (a.val 0) :=
  hillL2Discriminant_miura_zero a

theorem theorem4_i_central_action_zero (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    miuraNLSAction a 0 = 0 ↔ a.val 0 = 0 :=
  miuraNLSAction_zero_iff_mean_zero a ha

theorem theorem4_i_action_reflection (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℤ) :
    miuraNLSAction a (-n) = miuraNLSAction a n :=
  miuraNLSAction_reflection a ha n

theorem theorem4_i_positive_action_zero_iff_hillGap_collapsed (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    miuraNLSAction a n = 0 ↔ miuraHillLabels a ha (2*n-1) = miuraHillLabels a ha (2*n) :=
  miuraNLSAction_zero_iff_hillGap_collapsed a ha n hn

end NLS.Articles.MKdVNLSHierarchies
