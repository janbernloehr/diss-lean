import NLS.KdV.HillDirichletHamiltonianSources
import NLS.KdV.HillRealClosedCurveSources

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillDirichletGradientSpatialCurve_real
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (t : Icc (0:ℝ) 1) :
    (hillDirichletGradientSpatialCurve q n hn t).im = 0 := by
  have hA := hillL2FrequencyStateCurve_real (SpectralWeight.one.toCoeff q.val) q.property.2
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))
    (by rw [NLS.ComplexAnalysis.complex_sqrt_sq];rfl) (0,1) (by norm_num) t
  change (hillDirichletStateCurve q n hn t).1.im = 0 ∧
    (hillDirichletStateCurve q n hn t).2.im = 0 at hA
  change ((2/(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ))*
    ((hillDirichletStateCurve q n hn t).1*(hillDirichletStateCurve q n hn t).2)).im = 0
  simp only [mul_im,div_im,ofReal_im,im_ofNat,hA.1,hA.2,mul_zero,zero_mul,add_zero,sub_zero,zero_div]

theorem isReal_hillDirichletHamiltonianSource
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    IsRealHillPotential (SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q n hn)) := by
  apply isReal_hillClosedCurveCoefficients
  intro t
  change (-(hillDirichletGradientSpatialCurve q n hn t)).im = 0
  rw [neg_im,hillDirichletGradientSpatialCurve_real q n hn t,neg_zero]

theorem hillDirichletHamiltonianSource_mean_zero
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    (hillDirichletHamiltonianSource q n hn).val 0 = 0 := by
  rw [hillDirichletHamiltonianSource,hillClosedCurveCoefficients_zero]
  change (∫ x in (0:ℝ)..1,-NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q n hn) x) = 0
  rw [intervalIntegral.integral_neg]
  apply neg_eq_zero.mpr
  have hd := ae_hasDerivAt_hillDirichletGradientCurve q n hn
  rw [restrict_Ioc_eq_restrict_Icc] at hd
  have he := (ae_restrict_iff' measurableSet_Icc).mp hd
  have hh := integral_eq_sub_of_ac_of_ae_hasDerivAt
    (absolutelyContinuousOnInterval_hillDirichletGradientCurve q n hn)
    ((continuous_extend (hillDirichletGradientSpatialCurve q n hn)).intervalIntegrable 0 1)
    (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using he)
  rw [hh]
  dsimp only [NLS.LinearVolterra.extend]
  rw [projIcc_of_mem _ (show (1:ℝ) ∈ Icc 0 1 by norm_num),
    projIcc_of_mem _ (show (0:ℝ) ∈ Icc 0 1 by norm_num),
    (hillDirichletGradientCurve_endpoints q n hn).1,
    (hillDirichletGradientCurve_endpoints q n hn).2,sub_self]

end NLS.KdV
