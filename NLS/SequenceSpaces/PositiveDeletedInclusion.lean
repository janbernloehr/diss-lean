import NLS.SequenceSpaces.PositiveDeletedSpace

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.Coeff



variable (p : ℝ≥0∞) [Fact (1≤p)]

theorem positiveProjection_fixed_of_positiveDeleted (n : ℤ) (a : PositiveDeletedCoeff p n) :
    positiveDeletedProjection p (0 : ℤ) (a : Coeff p)=a := by
  apply (positiveDeletedProjection_eq_self_iff p 0 a).mpr
  intro m hm
  exact (positiveDeletedProjection_eq_self_iff p n a).mp (positiveDeleted_fixed p n a) m (Or.inl (by omega))

/-- The natural isometric inclusion of a positive-deleted coefficient
space in the full positive coefficient space. -/
def positiveDeletedToPositive (n : ℤ) : PositiveDeletedCoeff p n →L[ℂ] PositiveDeletedCoeff p (0 : ℤ) :=
  (positiveDeletedProjectionTo p (0 : ℤ)).comp
    (ContinuousLinearMap.id ℂ (Coeff p)-positiveDeletedProjection p n).ker.subtypeL

theorem positiveDeletedToPositive_coe (n : ℤ) (a : PositiveDeletedCoeff p n) :
    (positiveDeletedToPositive p n a : Coeff p)=a :=
  positiveProjection_fixed_of_positiveDeleted p n a

theorem norm_positiveDeletedToPositive (n : ℤ) (a : PositiveDeletedCoeff p n) :
    ‖positiveDeletedToPositive p n a‖=‖a‖ := by
  change ‖(positiveDeletedToPositive p n a : Coeff p)‖=‖(a : Coeff p)‖
  rw [positiveDeletedToPositive_coe]

end NLS.Coeff
