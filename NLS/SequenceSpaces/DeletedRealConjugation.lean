import NLS.SequenceSpaces.DeletedCoordinate
import NLS.SequenceSpaces.PeriodOneL2RealFormIdentity

/-! # Physical conjugation on the mean-zero L2 Hilbert space -/
noncomputable section
namespace NLS

def deletedL2Conjugation (a : DeletedCoeff 2 0) : DeletedCoeff 2 0 :=
  ⟨periodOneL2Conjugation a.val,by
    change periodOneL2Conjugation a.val 0 = 0
    rw [periodOneL2Conjugation_apply,neg_zero,show a.val 0 = 0 from a.property,map_zero]⟩

@[simp] theorem deletedL2Conjugation_val (a : DeletedCoeff 2 0) :
    (deletedL2Conjugation a).val = periodOneL2Conjugation a.val := rfl

@[simp] theorem norm_deletedL2Conjugation (a : DeletedCoeff 2 0) :
    ‖deletedL2Conjugation a‖ = ‖a‖ := norm_periodOneL2Conjugation a.val

@[simp] theorem deletedL2Conjugation_involutive (a : DeletedCoeff 2 0) :
    deletedL2Conjugation (deletedL2Conjugation a) = a :=
  Subtype.ext (periodOneL2Conjugation_involutive a.val)

@[simp] theorem deletedL2Conjugation_zero : deletedL2Conjugation 0 = 0 :=
  Subtype.ext periodOneL2Conjugation_zero

theorem deletedL2Conjugation_fixed_iff (a : DeletedCoeff 2 0) :
    deletedL2Conjugation a = a ↔ periodOneL2Conjugation a.val = a.val :=
  Subtype.ext_iff

theorem deleteCoordinateTo_conjugation (a : Coeff 2) :
    Coeff.deleteCoordinateTo 0 (periodOneL2Conjugation a) =
      deletedL2Conjugation (Coeff.deleteCoordinateTo 0 a) := by
  ext j
  change Coeff.deleteCoordinate 0 (periodOneL2Conjugation a) j =
    periodOneL2Conjugation (Coeff.deleteCoordinate 0 a) j
  by_cases hj : j = 0
  · subst j
    simp
  · change Coeff.deleteCoordinate 0 (periodOneL2Conjugation a) j =
      (starRingEnd ℂ) (Coeff.deleteCoordinate 0 a (-j))
    rw [Coeff.deleteCoordinate_apply_other 0 j hj]
    exact congrArg (starRingEnd ℂ) (Coeff.deleteCoordinate_apply_other 0 (-j) (neg_ne_zero.mpr hj) a).symm

end NLS
