import NLS.SequenceSpaces.PositiveDeletedProjection

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS



abbrev PositiveDeletedCoeff (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :=
  (ContinuousLinearMap.id ℂ (Coeff p)-Coeff.positiveDeletedProjection p n).ker

namespace Coeff

theorem positiveDeleted_fixed (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) (a : PositiveDeletedCoeff p n) :
    positiveDeletedProjection p n (a : Coeff p) = a := by
  have h := a.property
  change (a : Coeff p)-positiveDeletedProjection p n a = 0 at h
  exact (sub_eq_zero.mp h).symm

def positiveDeletedProjectionTo (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    Coeff p →L[ℂ] PositiveDeletedCoeff p n :=
  (positiveDeletedProjection p n).codRestrict _ (fun a => by
    change positiveDeletedProjection p n a-positiveDeletedProjection p n (positiveDeletedProjection p n a) = 0
    rw [positiveDeletedProjection_idempotent,sub_self])

theorem positiveDeletedProjectionTo_coe (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) (a : Coeff p) :
    (positiveDeletedProjectionTo p n a : Coeff p) = positiveDeletedProjection p n a := rfl

end Coeff

end NLS
