import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerRegularity
import NLS.SequenceSpaces.FourierRealExponentInclusion
import NLS.SequenceSpaces.SignedOrderHalfFourierEquiv

/-! Literal Wiener source/target models at every integer order, with
coefficient-preserving inclusions into the SAME actual Hilbert and rough
sources. The original free Fourier symbol is an equivalence at p=1. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def hillWienerSourceHilbertInclusion (N : ℕ) :
    fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1 →L[ℝ]
      RealSignedHilbert (signedStepOrder 0 N) :=
  fourierRealExponentInclusion _ (Weight.signedSobolev_neg _) (by norm_num : (1 : ℝ≥0∞) ≤ 2)

def hillWienerTargetHilbertInclusion (N : ℕ) :
    fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) 1 →L[ℝ]
      RealSignedHilbert (signedStepOrder (1/2) N) :=
  fourierRealExponentInclusion _ (Weight.signedSobolev_neg _) (by norm_num : (1 : ℝ≥0∞) ≤ 2)

theorem hillWienerSourceHilbertInclusion_apply (N : ℕ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1) (k : ℤ) :
    (hillWienerSourceHilbertInclusion N a).val.val.val k = a.val.val.val k :=
  fourierRealExponentInclusion_apply _ _ _ a k

theorem hillWienerTargetHilbertInclusion_apply (N : ℕ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) 1) (k : ℤ) :
    (hillWienerTargetHilbertInclusion N a).val.val.val k = a.val.val.val k :=
  fourierRealExponentInclusion_apply _ _ _ a k

theorem hillWienerSourceHilbertInclusion_injective (N : ℕ) :
    Function.Injective (hillWienerSourceHilbertInclusion N) :=
  fourierRealExponentInclusion_injective _ _ _

theorem hillWienerTargetHilbertInclusion_injective (N : ℕ) :
    Function.Injective (hillWienerTargetHilbertInclusion N) :=
  fourierRealExponentInclusion_injective _ _ _

def hillWienerSourceInclusion (N : ℕ) :
    fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1 →L[ℝ]
      HillRealMeanZeroSource :=
  (hillIntegerSourceInclusion N).comp (hillWienerSourceHilbertInclusion N)

theorem hillWienerSourceInclusion_apply (N : ℕ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1) (k : ℤ) :
    (hillWienerSourceInclusion N a).val.val.val k = a.val.val.val k := by
  rw [hillWienerSourceInclusion, ContinuousLinearMap.comp_apply,
    hillIntegerSourceInclusion_apply, hillWienerSourceHilbertInclusion_apply]

theorem hillIntegerSobolev_half_order (N : ℕ) :
    signedStepOrder (1/2) N = signedStepOrder 0 N + 1/2 := by
  rw [hillIntegerSobolev_source_order, hillIntegerSobolev_target_order]

def hillIntegerFreeFourierEquiv (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) p ≃L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) p :=
  signedRealOrderHalfFourierEquivOfEq _ _ (hillIntegerSobolev_half_order N) p

theorem hillIntegerFreeFourierEquiv_apply (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) p) (k : ℤ) :
    (hillIntegerFreeFourierEquiv N p a).val.val.val k = halfFourierSymbol k * a.val.val.val k :=
  signedRealOrderHalfFourierEquivOfEq_apply _ _ _ p a k

theorem hillIntegerFreeFourierEquiv_symm_apply (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) p) (k : ℤ) :
    ((hillIntegerFreeFourierEquiv N p).symm a).val.val.val k = halfFourierInverseSymbol k * a.val.val.val k :=
  signedRealOrderHalfFourierEquivOfEq_symm_apply _ _ _ p a k

theorem hillIntegerFreeFourierEquiv_Wiener_compatibility (N : ℕ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1) :
    hillWienerTargetHilbertInclusion N (hillIntegerFreeFourierEquiv N 1 a) =
      hillIntegerFreeFourierEquiv N 2 (hillWienerSourceHilbertInclusion N a) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillWienerTargetHilbertInclusion_apply, hillIntegerFreeFourierEquiv_apply,
    hillIntegerFreeFourierEquiv_apply, hillWienerSourceHilbertInclusion_apply]

end NLS.Articles.KdVPseudomeasures
