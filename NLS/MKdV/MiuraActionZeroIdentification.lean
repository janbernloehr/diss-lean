import NLS.MKdV.MiuraZeroEnergy
import NLS.MKdV.MiuraGapIdentification
import NLS.ZakharovShabat.SourceIndexedActionAnalytic

/-! # Vanishing of the actual restricted NLS actions

The actions are the existing source contour integrals. The central action
vanishes exactly at zero physical mean; every positive action vanishes
exactly when the independently constructed Miura Hill gap collapses.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraNLSAction (a : ScalarDomain 2) (n : ℤ) : ℂ :=
  sourceIndexedAction (by simp) (by norm_num) n (sobolevSourceInclusion (a,a))

theorem miuraNLSAction_nonnegative (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℤ) :
    0 ≤ (miuraNLSAction a n).re ∧ (miuraNLSAction a n).im = 0 := by
  have h := sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) n
    (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property
  exact ⟨h.1,h.2.1⟩

theorem miuraNLSAction_zero_iff_endpoints (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℤ) :
    miuraNLSAction a n = 0 ↔ miuraNLSLeft a n = miuraNLSRight a n := by
  have h := (sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) n
    (realDiagonalH1Source a ha).val (realDiagonalH1Source a ha).property).2.2
  have he : miuraNLSAction a n = 0 ↔ miuraNLSRight a n = miuraNLSLeft a n := by
    simpa only [miuraNLSAction,sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,
      miuraNLSLeft,miuraNLSRight,realDiagonalH1Source,sub_eq_zero] using h
  exact he.trans eq_comm

theorem miuraNLSAction_zero_iff_mean_zero (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    miuraNLSAction a 0 = 0 ↔ a.val 0 = 0 :=
  (miuraNLSAction_zero_iff_endpoints a ha 0).trans (miura_ground_collapsed_iff_mean_zero a ha)

theorem miuraNLSAction_zero_iff_hillGap_collapsed (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    miuraNLSAction a n = 0 ↔ miuraHillLabels a ha (2*n-1) = miuraHillLabels a ha (2*n) :=
  (miuraNLSAction_zero_iff_endpoints a ha n).trans (miuraHillGap_collapsed_iff a ha n hn).symm

end NLS.MKdV
