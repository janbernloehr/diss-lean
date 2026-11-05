import NLS.MKdV.MiuraH1ActionSequence
import NLS.ZakharovShabat.SourceSpatialZeroGaps

/-! # Vanishing physical actions at constant real scalar profiles

The physical derivative zero condition forces every positive Hill action
to vanish. The entire native weighted action sequence is then zero,
including at zero mean, with no explicit spectral labeling at constants.
-/
noncomputable section
open Set NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- Every positive physical Hill contour action vanishes at a constant scalar source. -/
theorem miuraMKdVAction_eq_zero_of_derivative_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (hd : periodOneDerivative a = 0)
    (n : ℕ) (hn : 1 ≤ n) : miuraMKdVAction a ha n = 0 := by
  let b : realTypeSobolevSourceLocus := ⟨(a,a),(realDiagonalH1Source a ha).property⟩
  have hb : sourceSobolevSpatialDerivative b.val = 0 := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext
    · exact hd
    · exact hd
  have hgap := sourcePeriodicGap_eq_zero_of_spatialDerivative_zero b hb (n : ℤ) (by omega)
  change miuraNLSRight a n-miuraNLSLeft a n = 0 at hgap
  have hI := (miuraNLSAction_zero_iff_endpoints a ha n).mpr (sub_eq_zero.mp hgap).symm
  exact (miuraMKdVAction_nonnegative_and_zero_iff a ha n hn).2.2.mpr hI

/-- The actual weighted physical action sequence at a constant profile is zero. -/
theorem miuraH1ActionSequence_eq_zero_of_derivative_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (hd : periodOneDerivative a = 0) :
    miuraH1ActionSequence a = 0 := by
  apply Subtype.ext
  funext n
  by_cases hn : 0 < n
  · have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
    rw [← he,miuraH1ActionSequence_physical a ha n.toNat (by omega),
      miuraMKdVAction_eq_zero_of_derivative_zero a ha hd n.toNat (by omega)]
    rfl
  · exact miuraH1ActionSequence_nonpositive a n hn

end NLS.MKdV
