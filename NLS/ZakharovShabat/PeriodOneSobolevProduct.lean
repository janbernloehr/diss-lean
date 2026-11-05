import NLS.ZakharovShabat.SourceSobolevSpatialGraph
import NLS.SequenceSpaces.SobolevConvolution

/-! # Bounded multiplication in the original complex H¹ space

The existing coefficient product and its exact period-one Leibniz graph
are recovered by one bounded linear graph operator. This makes the actual
H¹ product a continuous complex bilinear map without changing coefficients.
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

private def sobolevProductBase : ScalarDomain 2 →L[ℂ] ScalarDomain 2 →L[ℂ] Coeff 2 :=
  (Coeff.convolutionCLM (p := 2)).bilinearComp scalarInclusion (WeightedCoeff.sobolevToL1CLM 2 (by simp))

private def sobolevProductSpatial : ScalarDomain 2 →L[ℂ] ScalarDomain 2 →L[ℂ] Coeff 2 :=
  (2 : ℂ) • ((Coeff.convolutionCLM (p := 2)).bilinearComp derivative (WeightedCoeff.sobolevToL1CLM 2 (by simp)) +
    (Coeff.youngConvolutionCLM (show YoungRelation 1 2 2 by simp [YoungRelation])).bilinearComp
      (WeightedCoeff.sobolevToL1CLM 2 (by simp)) derivative)

def periodOneSobolevProduct : ScalarDomain 2 →L[ℂ] ScalarDomain 2 →L[ℂ] ScalarDomain 2 :=
  ((ContinuousLinearMap.compL ℂ (ScalarDomain 2) (Coeff 2) (ScalarDomain 2)
    (spatialGraphRecovery.comp (ContinuousLinearMap.inl ℂ _ _))).comp sobolevProductBase) +
  ((ContinuousLinearMap.compL ℂ (ScalarDomain 2) (Coeff 2) (ScalarDomain 2)
    (spatialGraphRecovery.comp (ContinuousLinearMap.inr ℂ _ _))).comp sobolevProductSpatial)

theorem periodOneSobolevProduct_eq_convolution (a b : ScalarDomain 2) :
    periodOneSobolevProduct a b = sobolevConvolution (by simp) a b := by
  have hd : sobolevProductSpatial a b = periodOneDerivative (sobolevConvolution (by simp) a b) := by
    change (2 : ℂ) • (_+_) = (2 : ℂ) • derivative (sobolevConvolution (by simp) a b)
    rw [derivative_sobolevConvolution]
    rfl
  have hb : sobolevProductBase a b = scalarInclusion (sobolevConvolution (by simp) a b) :=
    (scalarInclusion_sobolevConvolution (by simp) a b).symm
  change spatialGraphRecovery (sobolevProductBase a b,0)+spatialGraphRecovery (0,sobolevProductSpatial a b) = _
  rw [← map_add,hb,hd]
  simpa only [Prod.mk_add_mk,add_zero,zero_add] using spatialGraphRecovery_leftInverse (sobolevConvolution (by simp) a b)

@[simp] theorem periodOneSobolevProduct_apply (a b : ScalarDomain 2) (n : ℤ) :
    (periodOneSobolevProduct a b).val n = ∑' k : ℤ, a.val (n-k)*b.val k := by
  rw [periodOneSobolevProduct_eq_convolution,sobolevConvolution_apply]

theorem scalarInclusion_periodOneSobolevProduct (a b : ScalarDomain 2) :
    scalarInclusion (periodOneSobolevProduct a b) =
      Coeff.convolution (scalarInclusion a) (WeightedCoeff.sobolevToL1CLM 2 (by simp) b) := by
  rw [periodOneSobolevProduct_eq_convolution,scalarInclusion_sobolevConvolution]

theorem periodOneSobolevProduct_comm (a b : ScalarDomain 2) :
    periodOneSobolevProduct a b = periodOneSobolevProduct b a := by
  apply Subtype.ext
  funext n
  rw [periodOneSobolevProduct_apply,periodOneSobolevProduct_apply,
    ← (Equiv.subLeft n).tsum_eq (fun k : ℤ => b.val (n-k)*a.val k)]
  apply tsum_congr
  intro k
  simp only [Equiv.subLeft_apply,sub_sub_cancel,mul_comm]

/-- The exact physical Leibniz rule is retained in L², not only coefficientwise. -/
theorem periodOneDerivative_periodOneSobolevProduct (a b : ScalarDomain 2) :
    periodOneDerivative (periodOneSobolevProduct a b) =
      Coeff.convolution (periodOneDerivative a) (WeightedCoeff.sobolevToL1CLM 2 (by simp) b) +
      Coeff.youngConvolution (show YoungRelation 1 2 2 by simp [YoungRelation])
        (WeightedCoeff.sobolevToL1CLM 2 (by simp) a) (periodOneDerivative b) := by
  rw [periodOneSobolevProduct_eq_convolution]
  simpa only [periodOneDerivative,smul_apply,smul_add,Coeff.convolution_smul_left,Coeff.youngConvolution_smul_right] using!
    congrArg (fun q : Coeff 2 => (2 : ℂ) • q) (derivative_sobolevConvolution (by simp) a b)


end NLS.ZakharovShabat
