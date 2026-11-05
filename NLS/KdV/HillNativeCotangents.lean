import NLS.KdV.HillGradientSecondRegularity
import NLS.KdV.HillDirichletGardnerBrackets
import NLS.Fourier.PeriodOneH2CurveData

/-! # Native H² representatives of the original Hill cotangents

The coefficients are the literal unit Fourier integrals of the independent
Dirichlet-energy and log-norming gradients. Their physical representatives
and first derivatives are recovered pointwise, including both endpoints.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

def hillDirichletH2Data (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    PeriodOneH2CurveData where
  profile := hillDirichletGradientCurve q n hn
  spatial := hillDirichletGradientSpatialCurve q n hn
  second := hillDirichletGradientSecond q n hn
  profile_ac := absolutelyContinuousOnInterval_hillDirichletGradientCurve q n hn
  spatial_ac := absolutelyContinuousOnInterval_hillDirichletGradientSpatialCurve q n hn
  second_memLp := memLp_hillDirichletGradientSecond q n hn
  hasDeriv := ae_hasDerivAt_hillDirichletGradientCurve q n hn
  hasSecondDeriv := ae_hasDerivAt_hillDirichletGradientSpatialCurve q n hn
  profile_periodic := (hillDirichletGradientCurve_endpoints q n hn).2.trans
    (hillDirichletGradientCurve_endpoints q n hn).1.symm
  spatial_periodic := (hillDirichletGradientSpatialCurve_endpoints q n hn).2.trans
    (hillDirichletGradientSpatialCurve_endpoints q n hn).1.symm

def hillLogNormingH2Data (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    PeriodOneH2CurveData where
  profile := hillLogNormingGradientCurve q n hn
  spatial := hillLogNormingGradientSpatialCurve q n hn
  second := hillLogNormingGradientSecond q n hn
  profile_ac := absolutelyContinuousOnInterval_hillLogNormingGradientCurve q n hn
  spatial_ac := absolutelyContinuousOnInterval_hillLogNormingGradientSpatialCurve q n hn
  second_memLp := memLp_hillLogNormingGradientSecond q n hn
  hasDeriv := ae_hasDerivAt_hillLogNormingGradientCurve q n hn
  hasSecondDeriv := ae_hasDerivAt_hillLogNormingGradientSpatialCurve q n hn
  profile_periodic := (hillLogNormingGradientCurve_endpoints q n hn).2.trans
    (hillLogNormingGradientCurve_endpoints q n hn).1.symm
  spatial_periodic := (hillLogNormingGradientSpatialCurve_endpoints q n hn).2.trans
    (hillLogNormingGradientSpatialCurve_endpoints q n hn).1.symm

def hillDirichletNativeGradient (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    ScalarSobolev 2 := (hillDirichletH2Data q n hn).native

def hillLogNormingNativeGradient (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    ScalarSobolev 2 := (hillLogNormingH2Data q n hn).native

theorem hillDirichletNativeGradient_apply (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (j : ℤ) :
    (hillDirichletNativeGradient q n hn).val j =
      periodOneCoefficient (extend (hillDirichletGradientCurve q n hn)) j := rfl

theorem hillLogNormingNativeGradient_apply (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (j : ℤ) :
    (hillLogNormingNativeGradient q n hn).val j =
      periodOneCoefficient (extend (hillLogNormingGradientCurve q n hn)) j := rfl

end NLS.KdV
