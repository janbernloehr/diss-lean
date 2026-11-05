import NLS.SequenceSpaces.PeriodOneHminusOneRealForm
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # The closed mean-zero unit-period H^-1 phase space -/
noncomputable section
set_option autoImplicit false
namespace NLS

abbrev PeriodOneMeanZeroHminusOne :=
  (WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 0).ker

instance : CompleteSpace PeriodOneMeanZeroHminusOne := inferInstance

def periodOneMeanZeroInclusion : PeriodOneMeanZeroHminusOne →L[ℂ] PeriodOneHminusOne :=
  (WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 0).ker.subtypeL

@[simp] theorem periodOneMeanZeroInclusion_apply (q : PeriodOneMeanZeroHminusOne) :
    periodOneMeanZeroInclusion q = q.val := rfl

@[simp] theorem periodOneMeanZeroHminusOne_zero_coefficient (q : PeriodOneMeanZeroHminusOne) :
    q.val.val 0 = 0 := q.property

end NLS
