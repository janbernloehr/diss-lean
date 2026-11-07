import NLS.SequenceSpaces.HalfFourierEquiv
import NLS.SequenceSpaces.WeightedZeroMode

/-! The exact weighted Fourier isomorphism restricts to the closed
mean-zero source and signed zero-mode target, with bounded inverse. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem halfFourierEquiv_map_zeroMode :
    (zeroModeSubmodule (Weight.sobolev (-1)) p).map (halfFourierEquiv p).toLinearMap=
      zeroModeSubmodule (Weight.signedSobolev (-1/2)) p := by
  apply le_antisymm
  · rintro b ⟨a,ha,rfl⟩
    change (halfFourierEquiv p a).val 0=0
    rw [halfFourierEquiv_apply,show a.val 0=0 from ha,mul_zero]
  · intro b hb
    refine ⟨(halfFourierEquiv p).symm b,?_,(halfFourierEquiv p).apply_symm_apply b⟩
    change ((halfFourierEquiv p).symm b).val 0=0
    rw [halfFourierEquiv_symm_apply,show b.val 0=0 from hb,mul_zero]

def meanZeroHalfFourierEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    zeroModeSubmodule (Weight.sobolev (-1)) p ≃L[ℂ]
      zeroModeSubmodule (Weight.signedSobolev (-1/2)) p :=
  (halfFourierEquiv p).ofSubmodules _ _ halfFourierEquiv_map_zeroMode

theorem meanZeroHalfFourierEquiv_apply (a : zeroModeSubmodule (Weight.sobolev (-1)) p) (k : ℤ) :
    ((meanZeroHalfFourierEquiv p a : WeightedCoeff (Weight.signedSobolev (-1/2)) p)).val k=
      halfFourierSymbol k*a.val.val k := rfl

theorem meanZeroHalfFourierEquiv_symm_apply
    (a : zeroModeSubmodule (Weight.signedSobolev (-1/2)) p) (k : ℤ) :
    (((meanZeroHalfFourierEquiv p).symm a : WeightedCoeff (Weight.sobolev (-1)) p)).val k=
      halfFourierInverseSymbol k*a.val.val k := rfl

end NLS.WeightedCoeff
