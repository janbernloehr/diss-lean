import NLS.KdV.HillNativeMeanZeroComplexMap
import NLS.SequenceSpaces.RealMeanZeroHalfFourierEquiv

/-! The ACTUAL signed map on the closed physical real mean-zero source,
with its true real signed target. Its derivative is the exact real Fourier
Banach equivalence, not an unrelated componentwise-real restriction. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

abbrev HillRealMeanZeroSource := WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-1)) 2
abbrev HillRealSignedTarget := WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (-1/2)) 2

theorem hillMeanZeroComplexMap_mem_real (q : HillRealMeanZeroSource) :
    hillMeanZeroComplexMap q.val ∈ WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (-1/2)) 2 := by
  intro k
  change (hillMeanZeroComplexMap q.val).val.val (-k)=(starRingEnd ℂ) ((hillMeanZeroComplexMap q.val).val.val k)
  rw [hillMeanZeroComplexMap_coe]
  exact hillHminusNativeComplexMap_real q.val.val q.property k

def hillRealSignedMap (q : HillRealMeanZeroSource) : HillRealSignedTarget :=
  WeightedCoeff.fourierRealZeroProjection (p := 2) (Weight.signedSobolev (-1/2)) (Weight.signedSobolev_neg (-1/2))
    (hillMeanZeroComplexMap q.val)

theorem hillRealSignedMap_coe (q : HillRealMeanZeroSource) :
    (hillRealSignedMap q : HillSignedComplexTarget)=hillMeanZeroComplexMap q.val :=
  WeightedCoeff.fourierRealZeroProjection_coe _ _ _ (hillMeanZeroComplexMap_mem_real q)

theorem analyticAt_hillRealSignedMap (q : HillRealMeanZeroSource) : AnalyticAt ℝ hillRealSignedMap q := by
  have hq := real_mem_hillMeanZeroComplexDomain q.val q.property
  have hP : AnalyticAt ℝ
      (WeightedCoeff.fourierRealZeroProjection (p := 2) (Weight.signedSobolev (-1/2)) (Weight.signedSobolev_neg (-1/2)))
      (hillMeanZeroComplexMap q.val) := _root_.ContinuousLinearMap.analyticAt _ _
  have hI : AnalyticAt ℝ
      ((WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-1)) 2).subtypeL :
        HillRealMeanZeroSource →L[ℝ] HillMeanZeroSource) q := _root_.ContinuousLinearMap.analyticAt _ _
  have hN : AnalyticAt ℝ (fun a : HillRealMeanZeroSource => hillMeanZeroComplexMap a.val) q :=
    (analyticOnNhd_hillMeanZeroComplexMap q.val hq).restrictScalars.comp
      (f := fun a : HillRealMeanZeroSource => a.val) hI
  exact hP.comp (f := fun a : HillRealMeanZeroSource => hillMeanZeroComplexMap a.val) hN

theorem analyticOnNhd_hillRealSignedMap : AnalyticOnNhd ℝ hillRealSignedMap univ :=
  fun q _ => analyticAt_hillRealSignedMap q

theorem hillRealSignedMap_zero : hillRealSignedMap 0=0 := by
  unfold hillRealSignedMap
  rw [show ((0 : HillRealMeanZeroSource) : HillMeanZeroSource)=0 from rfl,
    hillMeanZeroComplexMap_zero,map_zero]

theorem fderiv_hillRealSignedMap_zero :
    fderiv ℝ hillRealSignedMap 0=(WeightedCoeff.realMeanZeroHalfFourierEquiv 2).toContinuousLinearMap := by
  let S := WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-1)) 2
  have hC := (analyticOnNhd_hillMeanZeroComplexMap 0 zero_mem_hillMeanZeroComplexDomain).differentiableAt.hasFDerivAt
  rw [fderiv_hillMeanZeroComplexMap_zero] at hC
  have hi : HasFDerivAt hillMeanZeroComplexMap
      ((WeightedCoeff.meanZeroHalfFourierEquiv 2).toContinuousLinearMap.restrictScalars ℝ) (S.subtypeL 0) := by
    simpa only [map_zero] using hC.restrictScalars ℝ
  have hI : HasFDerivAt (S.subtypeL : HillRealMeanZeroSource →L[ℝ] HillMeanZeroSource) S.subtypeL 0 :=
    _root_.ContinuousLinearMap.hasFDerivAt _
  have hP : HasFDerivAt
      (WeightedCoeff.fourierRealZeroProjection (p := 2) (Weight.signedSobolev (-1/2)) (Weight.signedSobolev_neg (-1/2)))
      (WeightedCoeff.fourierRealZeroProjection (p := 2) (Weight.signedSobolev (-1/2)) (Weight.signedSobolev_neg (-1/2)))
      (hillMeanZeroComplexMap (S.subtypeL 0)) := _root_.ContinuousLinearMap.hasFDerivAt _
  have hN : HasFDerivAt (fun q : HillRealMeanZeroSource => hillMeanZeroComplexMap q.val)
      (((WeightedCoeff.meanZeroHalfFourierEquiv 2).toContinuousLinearMap.restrictScalars ℝ).comp S.subtypeL) 0 :=
    hi.comp (𝕜 := ℝ) (E := HillRealMeanZeroSource) (F := HillMeanZeroSource) (G := HillSignedComplexTarget)
      (f := fun q : HillRealMeanZeroSource => q.val) 0 hI
  have hFinal : HasFDerivAt hillRealSignedMap
      ((WeightedCoeff.fourierRealZeroProjection (p := 2) (Weight.signedSobolev (-1/2)) (Weight.signedSobolev_neg (-1/2))).comp
        (((WeightedCoeff.meanZeroHalfFourierEquiv 2).toContinuousLinearMap.restrictScalars ℝ).comp S.subtypeL)) 0 := by
    exact @HasFDerivAt.comp ℝ inferInstance
      HillRealMeanZeroSource inferInstance inferInstance
      HillSignedComplexTarget inferInstance inferInstance
      HillRealSignedTarget inferInstance inferInstance
      (fun q : HillRealMeanZeroSource => hillMeanZeroComplexMap q.val)
      (((WeightedCoeff.meanZeroHalfFourierEquiv 2).toContinuousLinearMap.restrictScalars ℝ).comp S.subtypeL) 0
      _ _ hP hN
  have hd := hFinal.fderiv
  rw [hd]
  apply ContinuousLinearMap.ext
  intro h
  apply Subtype.ext
  change (WeightedCoeff.fourierRealZeroProjection (p := 2) (Weight.signedSobolev (-1/2))
    (Weight.signedSobolev_neg (-1/2)) (WeightedCoeff.meanZeroHalfFourierEquiv 2 h.val) : HillSignedComplexTarget)=_
  exact WeightedCoeff.fourierRealZeroProjection_coe _ _ _
    (WeightedCoeff.meanZeroHalfFourierEquiv_real h.val h.property)

end NLS.KdV
