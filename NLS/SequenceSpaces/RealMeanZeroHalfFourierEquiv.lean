import NLS.SequenceSpaces.MeanZeroHalfFourierEquiv
import NLS.FunctionalAnalysis.ComplexEquivRealRestriction
import NLS.SequenceSpaces.FourierRealZeroProjection

/-! The exact Fourier isomorphism and its bounded inverse preserve the
physical real mean-zero form, at every Banach exponent including infinity. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem halfFourierSymbol_conj (k : ℤ) : (starRingEnd ℂ) (halfFourierSymbol k)=halfFourierSymbol k :=
  Complex.conj_ofReal _

theorem halfFourierInverseSymbol_neg (k : ℤ) : halfFourierInverseSymbol (-k)=halfFourierInverseSymbol k := by
  simp only [halfFourierInverseSymbol,Int.cast_neg,abs_neg]

theorem halfFourierInverseSymbol_conj (k : ℤ) :
    (starRingEnd ℂ) (halfFourierInverseSymbol k)=halfFourierInverseSymbol k := Complex.conj_ofReal _

theorem meanZeroHalfFourierEquiv_real (a : zeroModeSubmodule (Weight.sobolev (-1)) p)
    (ha : a ∈ fourierRealZeroSubmodule (Weight.sobolev (-1)) p) :
    meanZeroHalfFourierEquiv p a ∈ fourierRealZeroSubmodule (Weight.signedSobolev (-1/2)) p := by
  intro k
  rw [meanZeroHalfFourierEquiv_apply,meanZeroHalfFourierEquiv_apply,halfFourierSymbol_neg,
    ha k,map_mul,halfFourierSymbol_conj]

theorem meanZeroHalfFourierEquiv_symm_real (a : zeroModeSubmodule (Weight.signedSobolev (-1/2)) p)
    (ha : a ∈ fourierRealZeroSubmodule (Weight.signedSobolev (-1/2)) p) :
    (meanZeroHalfFourierEquiv p).symm a ∈ fourierRealZeroSubmodule (Weight.sobolev (-1)) p := by
  intro k
  rw [meanZeroHalfFourierEquiv_symm_apply,meanZeroHalfFourierEquiv_symm_apply,halfFourierInverseSymbol_neg,
    ha k,map_mul,halfFourierInverseSymbol_conj]

theorem meanZeroHalfFourierEquiv_map_real :
    (fourierRealZeroSubmodule (Weight.sobolev (-1)) p).map
      (NLS.FunctionalAnalysis.complexEquivRealRestriction (meanZeroHalfFourierEquiv p)).toLinearMap=
        fourierRealZeroSubmodule (Weight.signedSobolev (-1/2)) p := by
  apply le_antisymm
  · rintro b ⟨a,ha,rfl⟩
    exact meanZeroHalfFourierEquiv_real a ha
  · intro b hb
    exact ⟨(meanZeroHalfFourierEquiv p).symm b,meanZeroHalfFourierEquiv_symm_real b hb,
      (meanZeroHalfFourierEquiv p).apply_symm_apply b⟩

def realMeanZeroHalfFourierEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    fourierRealZeroSubmodule (Weight.sobolev (-1)) p ≃L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev (-1/2)) p :=
  (NLS.FunctionalAnalysis.complexEquivRealRestriction (meanZeroHalfFourierEquiv p)).ofSubmodules _ _ meanZeroHalfFourierEquiv_map_real

theorem realMeanZeroHalfFourierEquiv_apply (a : fourierRealZeroSubmodule (Weight.sobolev (-1)) p) (k : ℤ) :
    (realMeanZeroHalfFourierEquiv p a).val.val.val k=halfFourierSymbol k*a.val.val.val k := rfl

theorem realMeanZeroHalfFourierEquiv_symm_apply
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (-1/2)) p) (k : ℤ) :
    ((realMeanZeroHalfFourierEquiv p).symm a).val.val.val k=halfFourierInverseSymbol k*a.val.val.val k := rfl

end NLS.WeightedCoeff
