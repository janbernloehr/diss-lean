import NLS.SequenceSpaces.FourierRealZeroCoordinates
import NLS.SequenceSpaces.ConjugateDuality
import NLS.SequenceSpaces.Reflection
import Mathlib.Analysis.InnerProductSpace.l2Space
import NLS.FunctionalAnalysis.RealBilinearQuadratic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Bounded bilinear quadratic forms on the FULL physical Fourier real
Hilbert spaces. Opposite indices, rather than componentwise-real inputs,
recover the exact squared Hilbert norm. -/
noncomputable section
open Complex
namespace NLS.Coeff

def oppositeHilbertPairing : Coeff 2 →L[ℂ] Coeff 2 →L[ℂ] ℂ :=
  (dualPairing (p:=2) (q:=2)).bilinearComp (ContinuousLinearMap.id ℂ _)
    reflection.toContinuousLinearEquiv.toContinuousLinearMap

theorem oppositeHilbertPairing_apply (a b : Coeff 2) :
    oppositeHilbertPairing a b=∑' k : ℤ, a k*b (-k) := by
  change dualPairing a (reflection b)= _
  rw [dualPairing_apply]
  apply tsum_congr
  intro k
  rw [reflection_apply]

theorem oppositeHilbertPairing_symm (a b : Coeff 2) :
    oppositeHilbertPairing a b=oppositeHilbertPairing b a := by
  rw [oppositeHilbertPairing_apply,oppositeHilbertPairing_apply,
    ← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => a k*b (-k))]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply,neg_neg,mul_comm]

theorem oppositeHilbertPairing_self_eq_norm_sq (a : Coeff 2)
    (ha : ∀ k : ℤ, a (-k)=(starRingEnd ℂ) (a k)) :
    oppositeHilbertPairing a a=((‖a‖^2:ℝ):ℂ) := by
  have he : oppositeHilbertPairing a a=inner ℂ a a := by
    rw [oppositeHilbertPairing_apply,lp.inner_eq_tsum]
    apply tsum_congr
    intro k
    rw [ha,RCLike.inner_apply']
    change a k*(starRingEnd ℂ) (a k)=(starRingEnd ℂ) (a k)*a k
    ring
  simpa only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow] using! he

theorem summable_norm_oppositeHilbertPairing (a b : Coeff 2) :
    Summable (fun k : ℤ => ‖a k*b (-k)‖) := by
  simpa only [reflection_apply] using summable_norm_dualPairing a (reflection b)

end NLS.Coeff
namespace NLS.WeightedCoeff

def fourierRealZeroWeightedCoefficients (w : Weight) : fourierRealZeroSubmodule w 2 →L[ℝ] Coeff 2 :=
  ((weightIsometry w 2).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
    (((zeroModeSubmodule w 2).subtypeL.restrictScalars ℝ).comp (fourierRealZeroSubmodule w 2).subtypeL)

theorem fourierRealZeroWeightedCoefficients_apply (w : Weight)
    (a : fourierRealZeroSubmodule w 2) (k : ℤ) :
    fourierRealZeroWeightedCoefficients w a k=(w k:ℂ)*a.val.val.val k := rfl

theorem norm_fourierRealZeroWeightedCoefficients (w : Weight) (a : fourierRealZeroSubmodule w 2) :
    ‖fourierRealZeroWeightedCoefficients w a‖=‖a‖ := by
  change ‖weightIsometry w 2 a.val.val‖=‖a.val.val‖
  exact (weightIsometry w 2).norm_map _

def fourierRealZeroHilbertPairing (w : Weight) :
    fourierRealZeroSubmodule w 2 →L[ℝ] fourierRealZeroSubmodule w 2 →L[ℝ] ℂ :=
  @NLS.FunctionalAnalysis.realBilinearPullback (fourierRealZeroSubmodule w 2) (Coeff 2)
    inferInstance inferInstance inferInstance inferInstance (Coeff.oppositeHilbertPairing.bilinearRestrictScalars ℝ)
    (fourierRealZeroWeightedCoefficients w)

theorem fourierRealZeroHilbertPairing_apply (w : Weight) (a b : fourierRealZeroSubmodule w 2) :
    fourierRealZeroHilbertPairing w a b=
      ∑' k : ℤ, ((w k:ℂ)*a.val.val.val k)*((w (-k):ℂ)*b.val.val.val (-k)) := by
  change Coeff.oppositeHilbertPairing (fourierRealZeroWeightedCoefficients w a)
    (fourierRealZeroWeightedCoefficients w b)= _
  rw [Coeff.oppositeHilbertPairing_apply]
  rfl

theorem fourierRealZeroHilbertPairing_symm (w : Weight) (a b : fourierRealZeroSubmodule w 2) :
    fourierRealZeroHilbertPairing w a b=fourierRealZeroHilbertPairing w b a :=
  Coeff.oppositeHilbertPairing_symm _ _

theorem fourierRealZeroHilbertPairing_self_eq_norm_sq (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : fourierRealZeroSubmodule w 2) :
    fourierRealZeroHilbertPairing w a a=((‖a‖^2:ℝ):ℂ) := by
  have hr (k : ℤ) : fourierRealZeroWeightedCoefficients w a (-k)=
      (starRingEnd ℂ) (fourierRealZeroWeightedCoefficients w a k) := by
    rw [fourierRealZeroWeightedCoefficients_apply,fourierRealZeroWeightedCoefficients_apply,hw,a.property,map_mul]
    simp only [Complex.conj_ofReal]
  change Coeff.oppositeHilbertPairing (fourierRealZeroWeightedCoefficients w a)
    (fourierRealZeroWeightedCoefficients w a)= _
  rw [Coeff.oppositeHilbertPairing_self_eq_norm_sq _ hr,norm_fourierRealZeroWeightedCoefficients]

theorem summable_norm_fourierRealZeroHilbertPairing (w : Weight) (a b : fourierRealZeroSubmodule w 2) :
    Summable (fun k : ℤ => ‖((w k:ℂ)*a.val.val.val k)*((w (-k):ℂ)*b.val.val.val (-k))‖) := by
  have h := Coeff.summable_norm_oppositeHilbertPairing
    (fourierRealZeroWeightedCoefficients w a) (fourierRealZeroWeightedCoefficients w b)
  simpa only [fourierRealZeroWeightedCoefficients_apply] using h

end NLS.WeightedCoeff
