import NLS.KdV.HillEnergyTraceGradientRegularity
import NLS.KdV.HillNativeBranchGradients

/-! # Full native Hill trace cotangents and actual H¹ Miura pullbacks -/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis NLS.Fourier NLS.Poisson
open scoped ENNReal
namespace NLS.KdV

def hillDiscriminantH2Data (q : Coeff 2) (E : ℂ) : PeriodOneH2CurveData where
  profile := hillEnergyTraceGradientCurve q E
  spatial := hillEnergyTraceGradientSpatialCurve q E
  second := hillEnergyTraceGradientSecond q E
  profile_ac := absolutelyContinuousOnInterval_hillEnergyTraceGradientCurve q E
  spatial_ac := absolutelyContinuousOnInterval_hillEnergyTraceGradientSpatialCurve q E
  second_memLp := memLp_hillEnergyTraceGradientSecond q E
  hasDeriv := ae_hasDerivAt_hillEnergyTraceGradientCurve q E
  hasSecondDeriv := ae_hasDerivAt_hillEnergyTraceGradientSpatialCurve q E
  profile_periodic := (hillEnergyTraceGradientCurve_endpoints q E).2.trans
    (hillEnergyTraceGradientCurve_endpoints q E).1.symm
  spatial_periodic := (hillEnergyTraceGradientSpatialCurve_endpoints q E).2.trans
    (hillEnergyTraceGradientSpatialCurve_endpoints q E).1.symm

def hillDiscriminantNativeGradient (q : Coeff 2) (E : ℂ) : ScalarSobolev 2 :=
  (hillDiscriminantH2Data q E).native

theorem hillDiscriminantNativeGradient_apply (q : Coeff 2) (E : ℂ) (j : ℤ) :
    (hillDiscriminantNativeGradient q E).val j =
      periodOneCoefficient (extend (hillEnergyTraceGradientCurve q E)) j := rfl

theorem hasFDerivAt_hillDiscriminant_unit (p r : Coeff 2) (hp : Coeff.periodDouble r = p) (E : ℂ) :
    HasFDerivAt (fun b => hillL2Discriminant (Coeff.periodDouble b) E)
      (reflectedHilbertPairing (scalarInclusion (hillDiscriminantH2Data p E).inclusion)) r := by
  have ha : AnalyticAt ℂ (fun q : Coeff 2 => hillL2Discriminant q E) p :=
    (analyticOnNhd_hillL2Discriminant_joint (E,p) (mem_univ _)).comp
      (f := fun q : Coeff 2 => (E,q)) (analyticAt_const.prod analyticAt_id)
  exact hasFDerivAt_hillUnit_pullback_of_curve _ p r hp (hillDiscriminantH2Data p E)
    ha.differentiableAt (fun h => fderiv_hillL2Discriminant_potential_integral p h E)

end NLS.KdV
