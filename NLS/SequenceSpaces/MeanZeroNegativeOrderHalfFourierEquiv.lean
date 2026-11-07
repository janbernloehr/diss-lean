import NLS.SequenceSpaces.NegativeOrderHalfFourierEquiv
import NLS.SequenceSpaces.WeightedZeroMode

/-! Exact mean-zero Fourier equivalences at every negative source order. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem negativeOrderHalfFourierEquiv_map_zeroMode (r : ℝ) (hr : 0 ≤ r) :
    (zeroModeSubmodule (Weight.sobolev (-r)) p).map (negativeOrderHalfFourierEquiv r hr p).toLinearMap=
      zeroModeSubmodule (Weight.signedSobolev (1/2-r)) p := by
  apply le_antisymm
  · rintro b ⟨a,ha,rfl⟩
    change (negativeOrderHalfFourierEquiv r hr p a).val 0=0
    rw [negativeOrderHalfFourierEquiv_apply,show a.val 0=0 from ha,mul_zero]
  · intro b hb
    refine ⟨(negativeOrderHalfFourierEquiv r hr p).symm b,?_,
      (negativeOrderHalfFourierEquiv r hr p).apply_symm_apply b⟩
    change ((negativeOrderHalfFourierEquiv r hr p).symm b).val 0=0
    rw [negativeOrderHalfFourierEquiv_symm_apply,show b.val 0=0 from hb,mul_zero]

def meanZeroNegativeOrderHalfFourierEquiv (r : ℝ) (hr : 0 ≤ r) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    zeroModeSubmodule (Weight.sobolev (-r)) p ≃L[ℂ]
      zeroModeSubmodule (Weight.signedSobolev (1/2-r)) p :=
  (negativeOrderHalfFourierEquiv r hr p).ofSubmodules _ _ (negativeOrderHalfFourierEquiv_map_zeroMode r hr)

theorem meanZeroNegativeOrderHalfFourierEquiv_apply (r : ℝ) (hr : 0 ≤ r)
    (a : zeroModeSubmodule (Weight.sobolev (-r)) p) (k : ℤ) :
    (meanZeroNegativeOrderHalfFourierEquiv r hr p a).val.val k=halfFourierSymbol k*a.val.val k := rfl

theorem meanZeroNegativeOrderHalfFourierEquiv_symm_apply (r : ℝ) (hr : 0 ≤ r)
    (a : zeroModeSubmodule (Weight.signedSobolev (1/2-r)) p) (k : ℤ) :
    ((meanZeroNegativeOrderHalfFourierEquiv r hr p).symm a).val.val k=halfFourierInverseSymbol k*a.val.val k := rfl

end NLS.WeightedCoeff
