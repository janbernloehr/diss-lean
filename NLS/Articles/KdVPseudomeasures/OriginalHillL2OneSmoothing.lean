import NLS.KdV.HillL2NativeComplexOneSmoothing
import NLS.Articles.KdVPseudomeasures.OriginalHillWienerBaseSmoothing

/-! The actual real mean-zero L2 native map has an analytic
one-smoothing Fourier defect. This supplies the previously explicit
base premise and hence the literal signed Wiener analytic equivalences
at ALL integer orders. Physical-distribution transport remains separate. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

local instance : NormedSpace ℝ (RealSignedHilbert 0) :=
  fourierRealZeroSubmodule_normedSpace (Weight.signedSobolev 0)
local instance : NormedSpace ℝ (RealSignedHilbert ((1/2:ℝ)+1)) :=
  fourierRealZeroSubmodule_normedSpace (Weight.signedSobolev ((1/2:ℝ)+1))

private def l2Coefficients : RealSignedHilbert 0 →L[ℝ] Coeff 2 :=
  (((weightIsometry (Weight.signedSobolev 0) 2).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).comp
    ((((zeroModeSubmodule (Weight.signedSobolev 0) 2).subtypeL).restrictScalars ℝ).comp
      (fourierRealZeroSubmodule (Weight.signedSobolev 0) 2).subtypeL)

private theorem l2Coefficients_apply (q : RealSignedHilbert 0) (k : ℤ) :
    l2Coefficients q k = q.val.val.val k := by
  change (Weight.signedSobolev 0 k:ℂ)*q.val.val.val k = _
  simp only [Weight.signedSobolev,Real.rpow_zero,ofReal_one,one_mul]

private theorem l2Coefficients_real (q : RealSignedHilbert 0) :
    IsRealPeriodOneHminusOne (periodOneL2Inclusion (l2Coefficients q)) := by
  intro k
  rw [periodOneL2Inclusion_apply,periodOneL2Inclusion_apply,l2Coefficients_apply,l2Coefficients_apply]
  exact q.property k

private theorem source_inclusion_eq (q : RealSignedHilbert 0) :
    (hillL2SourceInclusion q).val.val = periodOneL2Inclusion (l2Coefficients q) := by
  apply Subtype.ext
  funext k
  rw [hillL2SourceInclusion_apply,periodOneL2Inclusion_apply,l2Coefficients_apply]

private theorem actual_native_coefficient (q : RealSignedHilbert 0) (k : ℤ) :
    ((hillIntegerSobolevEquiv 0).equiv q).val.val.val k =
      (hillHminusNativeComplexMap (periodOneL2Inclusion (l2Coefficients q))).val k := by
  have h := hillIntegerSobolevEquiv_apply 0 (show RealSignedHilbert (signedStepOrder 0 0) from q) k
  apply h.trans
  change (((hillRealSignedMap (hillL2SourceInclusion q) : HillSignedComplexTarget) :
    WeightedCoeff (Weight.signedSobolev (-1/2)) 2)).val k = _
  rw [hillRealSignedMap_coe,hillMeanZeroComplexMap_coe]
  exact congrArg (fun a : PeriodOneHminusOne => (hillHminusNativeComplexMap a).val k) (source_inclusion_eq q)

private def complexRemainder (q : RealSignedHilbert 0) :
    WeightedCoeff (Weight.signedSobolev ((1/2:ℝ)+1)) 2 :=
  signedOrderInclusion ((1/2:ℝ)+1) (3/2) (by norm_num) 2
    (hillL2NativeComplexFourierRemainder (l2Coefficients q))

private theorem complexRemainder_raw (q : RealSignedHilbert 0) (k : ℤ) :
    (complexRemainder q).val k = ((hillIntegerSobolevEquiv 0).equiv q).val.val.val k-
      halfFourierSymbol k*q.val.val.val k := by
  rw [complexRemainder,signedOrderInclusion_apply,
    hillL2NativeComplexFourierRemainder_apply _ (l2Coefficients_real q),l2Coefficients_apply]
  exact congrArg (fun z : ℂ => z-halfFourierSymbol k*q.val.val.val k) (actual_native_coefficient q k).symm

private theorem analytic_complexRemainder (q : RealSignedHilbert 0) : AnalyticAt ℝ complexRemainder q := by
  have hL := @ContinuousLinearMap.analyticAt ℝ inferInstance
    (RealSignedHilbert 0) inferInstance inferInstance (Coeff 2) inferInstance inferInstance l2Coefficients q
  have hF : AnalyticAt ℝ hillL2NativeComplexFourierRemainder (l2Coefficients q) :=
    (analyticAt_hillL2NativeComplexFourierRemainder _ (l2Coefficients_real q)).restrictScalars
  have hcomp : AnalyticAt ℝ (fun r : RealSignedHilbert 0 => hillL2NativeComplexFourierRemainder (l2Coefficients r)) q :=
    hF.comp (f := fun r : RealSignedHilbert 0 => l2Coefficients r) hL
  have hJ := @ContinuousLinearMap.analyticAt ℝ inferInstance
    (WeightedCoeff (Weight.signedSobolev (3/2)) 2) inferInstance inferInstance
    (WeightedCoeff (Weight.signedSobolev ((1/2:ℝ)+1)) 2) inferInstance inferInstance
    ((signedOrderInclusion ((1/2:ℝ)+1) (3/2) (by norm_num) 2).restrictScalars ℝ)
    (hillL2NativeComplexFourierRemainder (l2Coefficients q))
  exact hJ.comp (f := fun r : RealSignedHilbert 0 => hillL2NativeComplexFourierRemainder (l2Coefficients r)) hcomp

private theorem complexRemainder_zero (q : RealSignedHilbert 0) : (complexRemainder q).val 0 = 0 := by
  rw [complexRemainder_raw]
  have hz : ((hillIntegerSobolevEquiv 0).equiv q).val.val.val 0 = 0 :=
    ((hillIntegerSobolevEquiv 0).equiv q).val.property
  have hq : q.val.val.val 0 = 0 := q.val.property
  rw [hz,hq,mul_zero,sub_self]

private theorem complexRemainder_real (q : RealSignedHilbert 0) (k : ℤ) :
    (complexRemainder q).val (-k) = (starRingEnd ℂ) ((complexRemainder q).val k) := by
  rw [complexRemainder_raw,complexRemainder_raw,
    ((hillIntegerSobolevEquiv 0).equiv q).property k,q.property k,
      halfFourierSymbol_neg,map_sub,map_mul,halfFourierSymbol_conj]

private def realRemainder (q : RealSignedHilbert 0) : RealSignedHilbert ((1/2:ℝ)+1) :=
  fourierRealZeroProjection _ (Weight.signedSobolev_neg _) (zeroModeProjection _ (complexRemainder q))

private theorem realRemainder_coe (q : RealSignedHilbert 0) :
    (realRemainder q).val.val = complexRemainder q := by
  have hz : (zeroModeProjection _ (complexRemainder q) : WeightedCoeff (Weight.signedSobolev ((1/2:ℝ)+1)) 2) =
      complexRemainder q := zeroModeProjection_coe _ _ (complexRemainder_zero q)
  have hr : zeroModeProjection _ (complexRemainder q) ∈
      fourierRealZeroSubmodule (Weight.signedSobolev ((1/2:ℝ)+1)) 2 := by
    intro k
    rw [hz]
    exact complexRemainder_real q k
  change ((fourierRealZeroProjection _ (Weight.signedSobolev_neg _) (zeroModeProjection _ (complexRemainder q)) :
    zeroModeSubmodule (Weight.signedSobolev ((1/2:ℝ)+1)) 2) : WeightedCoeff (Weight.signedSobolev ((1/2:ℝ)+1)) 2) = _
  rw [fourierRealZeroProjection_coe _ _ _ hr,hz]

private theorem analytic_realRemainder (q : RealSignedHilbert 0) : AnalyticAt ℝ realRemainder q := by
  have hZ := @ContinuousLinearMap.analyticAt ℝ inferInstance
    (WeightedCoeff (Weight.signedSobolev ((1/2:ℝ)+1)) 2) inferInstance inferInstance
    (zeroModeSubmodule (Weight.signedSobolev ((1/2:ℝ)+1)) 2) inferInstance inferInstance
    ((zeroModeProjection (Weight.signedSobolev ((1/2:ℝ)+1)) (p := 2)).restrictScalars ℝ) (complexRemainder q)
  have hz := hZ.comp (f := complexRemainder) (analytic_complexRemainder q)
  have hP := @ContinuousLinearMap.analyticAt ℝ inferInstance
    (zeroModeSubmodule (Weight.signedSobolev ((1/2:ℝ)+1)) 2) inferInstance inferInstance
    (RealSignedHilbert ((1/2:ℝ)+1)) inferInstance inferInstance
    (fourierRealZeroProjection (Weight.signedSobolev ((1/2:ℝ)+1)) (Weight.signedSobolev_neg _) (p := 2))
    (zeroModeProjection (Weight.signedSobolev ((1/2:ℝ)+1)) (complexRemainder q))
  exact hP.comp (f := fun r : RealSignedHilbert 0 =>
    zeroModeProjection (Weight.signedSobolev ((1/2:ℝ)+1)) (complexRemainder r)) hz

theorem hillIntegerNativeOneSmoothing_zero : HillIntegerNativeOneSmoothing 0 := by
  refine ⟨realRemainder,analytic_realRemainder,?_⟩
  intro q k
  exact (congrArg (fun a : WeightedCoeff (Weight.signedSobolev ((1/2:ℝ)+1)) 2 => a.val k)
    (realRemainder_coe q)).trans (complexRemainder_raw q k)

theorem hillIntegerNativeOneSmoothing_all (N : ℕ) : HillIntegerNativeOneSmoothing N :=
  hillIntegerNativeOneSmoothing_all_of_base hillIntegerNativeOneSmoothing_zero N

theorem hillWienerBirkhoffDiffeomorphism_all (N : ℕ) : HillWienerBirkhoffDiffeomorphism N :=
  hillWienerBirkhoffDiffeomorphism_all_of_baseSmoothing hillIntegerNativeOneSmoothing_zero N

end NLS.Articles.KdVPseudomeasures
