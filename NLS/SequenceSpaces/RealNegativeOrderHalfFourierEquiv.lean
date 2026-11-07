import NLS.SequenceSpaces.MeanZeroNegativeOrderHalfFourierEquiv
import NLS.SequenceSpaces.RealMeanZeroHalfFourierEquiv

/-! The same Fourier equivalences preserve the physical real form,
at all nonpositive source orders and all Banach exponents. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem meanZeroNegativeOrderHalfFourierEquiv_real (r : ℝ) (hr : 0 ≤ r)
    (a : zeroModeSubmodule (Weight.sobolev (-r)) p)
    (ha : a ∈ fourierRealZeroSubmodule (Weight.sobolev (-r)) p) :
    meanZeroNegativeOrderHalfFourierEquiv r hr p a ∈ fourierRealZeroSubmodule (Weight.signedSobolev (1/2-r)) p := by
  intro k
  rw [meanZeroNegativeOrderHalfFourierEquiv_apply,meanZeroNegativeOrderHalfFourierEquiv_apply,
    halfFourierSymbol_neg,ha k,map_mul,halfFourierSymbol_conj]

theorem meanZeroNegativeOrderHalfFourierEquiv_symm_real (r : ℝ) (hr : 0 ≤ r)
    (a : zeroModeSubmodule (Weight.signedSobolev (1/2-r)) p)
    (ha : a ∈ fourierRealZeroSubmodule (Weight.signedSobolev (1/2-r)) p) :
    (meanZeroNegativeOrderHalfFourierEquiv r hr p).symm a ∈ fourierRealZeroSubmodule (Weight.sobolev (-r)) p := by
  intro k
  rw [meanZeroNegativeOrderHalfFourierEquiv_symm_apply,meanZeroNegativeOrderHalfFourierEquiv_symm_apply,
    halfFourierInverseSymbol_neg,ha k,map_mul,halfFourierInverseSymbol_conj]

theorem meanZeroNegativeOrderHalfFourierEquiv_map_real (r : ℝ) (hr : 0 ≤ r) :
    (fourierRealZeroSubmodule (Weight.sobolev (-r)) p).map
      (NLS.FunctionalAnalysis.complexEquivRealRestriction (meanZeroNegativeOrderHalfFourierEquiv r hr p)).toLinearMap=
        fourierRealZeroSubmodule (Weight.signedSobolev (1/2-r)) p := by
  apply le_antisymm
  · rintro b ⟨a,ha,rfl⟩
    exact meanZeroNegativeOrderHalfFourierEquiv_real r hr a ha
  · intro b hb
    exact ⟨(meanZeroNegativeOrderHalfFourierEquiv r hr p).symm b,
      meanZeroNegativeOrderHalfFourierEquiv_symm_real r hr b hb,
      (meanZeroNegativeOrderHalfFourierEquiv r hr p).apply_symm_apply b⟩

def realMeanZeroNegativeOrderHalfFourierEquiv (r : ℝ) (hr : 0 ≤ r) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    fourierRealZeroSubmodule (Weight.sobolev (-r)) p ≃L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev (1/2-r)) p :=
  (NLS.FunctionalAnalysis.complexEquivRealRestriction (meanZeroNegativeOrderHalfFourierEquiv r hr p)).ofSubmodules _ _
    (meanZeroNegativeOrderHalfFourierEquiv_map_real r hr)

theorem realMeanZeroNegativeOrderHalfFourierEquiv_apply (r : ℝ) (hr : 0 ≤ r)
    (a : fourierRealZeroSubmodule (Weight.sobolev (-r)) p) (k : ℤ) :
    (realMeanZeroNegativeOrderHalfFourierEquiv r hr p a).val.val.val k=halfFourierSymbol k*a.val.val.val k := rfl

theorem realMeanZeroNegativeOrderHalfFourierEquiv_symm_apply (r : ℝ) (hr : 0 ≤ r)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (1/2-r)) p) (k : ℤ) :
    ((realMeanZeroNegativeOrderHalfFourierEquiv r hr p).symm a).val.val.val k=
      halfFourierInverseSymbol k*a.val.val.val k := rfl

end NLS.WeightedCoeff
