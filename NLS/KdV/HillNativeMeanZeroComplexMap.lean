import NLS.KdV.HillNativeComplexFirstVariation
import NLS.SequenceSpaces.MeanZeroHalfFourierEquiv
import NLS.FunctionalAnalysis.LinearSourceRestrictionDerivative

/-! The actual signed complex map restricted to the correct complex
mean-zero Banach source and zero-mode target. Its derivative is a genuine
continuous linear equivalence, with the exact Fourier inverse. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

abbrev HillMeanZeroSource := WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2
abbrev HillSignedComplexTarget := WeightedCoeff.zeroModeSubmodule (Weight.signedSobolev (-1/2)) 2

def hillMeanZeroComplexDomain : Set HillMeanZeroSource :=
  {q | (q : PeriodOneHminusOne) ∈ hillHminusActionAngleNativeDomain}

def hillMeanZeroComplexMap (q : HillMeanZeroSource) : HillSignedComplexTarget :=
  WeightedCoeff.zeroModeProjection (Weight.signedSobolev (-1/2))
    (hillHminusNativeComplexMap (q : PeriodOneHminusOne))

theorem hillMeanZeroComplexMap_coe (q : HillMeanZeroSource) :
    (hillMeanZeroComplexMap q : WeightedCoeff (Weight.signedSobolev (-1/2)) 2)=
      hillHminusNativeComplexMap (q : PeriodOneHminusOne) :=
  WeightedCoeff.zeroModeProjection_coe _ _ (hillHminusNativeComplexMap_zero_mode _)

theorem isOpen_hillMeanZeroComplexDomain : IsOpen hillMeanZeroComplexDomain :=
  isOpen_hillHminusActionAngleNativeDomain.preimage
    (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL.continuous

theorem real_mem_hillMeanZeroComplexDomain (q : HillMeanZeroSource)
    (hq : IsRealPeriodOneHminusOne (q : PeriodOneHminusOne)) : q ∈ hillMeanZeroComplexDomain :=
  real_mem_hillHminusActionAngleNativeDomain _ hq

theorem zero_mem_hillMeanZeroComplexDomain : (0 : HillMeanZeroSource) ∈ hillMeanZeroComplexDomain := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  exact real_mem_hillHminusActionAngleNativeDomain 0 hr

theorem analyticOnNhd_hillMeanZeroComplexMap :
    AnalyticOnNhd ℂ hillMeanZeroComplexMap hillMeanZeroComplexDomain := by
  intro q hq
  exact ((WeightedCoeff.zeroModeProjection (Weight.signedSobolev (-1/2))).analyticAt _).comp
    ((analyticOnNhd_hillHminusNativeComplexMap _ hq).comp
      ((WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL.analyticAt q))

theorem hillMeanZeroComplexMap_zero : hillMeanZeroComplexMap 0=0 := by
  unfold hillMeanZeroComplexMap
  rw [show ((0 : HillMeanZeroSource) : PeriodOneHminusOne)=0 from rfl,
    hillHminusNativeComplexMap_zero,map_zero]

theorem fderiv_hillHminusNativeComplexMap_eq_halfFourier (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    (fderiv ℂ hillHminusNativeComplexMap 0) h=WeightedCoeff.halfFourierEquiv 2 h := by
  apply Subtype.ext
  funext k
  by_cases hk : k=0
  · subst k
    rw [fderiv_hillHminusNativeComplexMap_zero_mode,WeightedCoeff.halfFourierEquiv_apply,hh,mul_zero]
  · by_cases hp : 0 < k
    · let n : ℕ+ := ⟨k.toNat,by omega⟩
      have hn : ((n:ℕ):ℤ)=k := Int.toNat_of_nonneg hp.le
      rw [← hn,fderiv_hillHminusNativeComplexMap_positive_mean_zero n h hh,
        WeightedCoeff.halfFourierEquiv_apply,WeightedCoeff.halfFourierSymbol_positive]
      ring
    · let n : ℕ+ := ⟨(-k).toNat,by omega⟩
      have hn : -((n:ℕ):ℤ)=k := by
        have hn' : ((n:ℕ):ℤ) = -k := Int.toNat_of_nonneg (by omega)
        omega
      rw [← hn,fderiv_hillHminusNativeComplexMap_negative_mean_zero n h hh,
        WeightedCoeff.halfFourierEquiv_apply,WeightedCoeff.halfFourierSymbol_neg,
        WeightedCoeff.halfFourierSymbol_positive]
      ring

theorem fderiv_hillMeanZeroComplexMap_zero :
    fderiv ℂ hillMeanZeroComplexMap 0=(WeightedCoeff.meanZeroHalfFourierEquiv 2).toContinuousLinearMap := by
  let S := WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hN := (analyticOnNhd_hillHminusNativeComplexMap 0
    (real_mem_hillHminusActionAngleNativeDomain 0 hr)).differentiableAt
  have hi : HasFDerivAt hillHminusNativeComplexMap (fderiv ℂ hillHminusNativeComplexMap 0)
      (S.subtypeL 0) := by simpa only [map_zero] using hN.hasFDerivAt
  have hd := ((WeightedCoeff.zeroModeProjection (Weight.signedSobolev (-1/2))).hasFDerivAt.comp 0
    (hi.comp 0 S.subtypeL.hasFDerivAt)).fderiv
  change fderiv ℂ hillMeanZeroComplexMap 0 = _ at hd
  rw [hd]
  apply ContinuousLinearMap.ext
  intro h
  apply Subtype.ext
  change (WeightedCoeff.zeroModeProjection (Weight.signedSobolev (-1/2))
    ((fderiv ℂ hillHminusNativeComplexMap 0) h.val) : WeightedCoeff (Weight.signedSobolev (-1/2)) 2)=_
  rw [fderiv_hillHminusNativeComplexMap_eq_halfFourier h.val h.property]
  exact WeightedCoeff.zeroModeProjection_coe _ _ (by
    rw [WeightedCoeff.halfFourierEquiv_apply,show h.val.val 0=0 from h.property,mul_zero])

end NLS.KdV
