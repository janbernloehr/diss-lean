import NLS.ComplexAnalysis.QuadraticHillKdVFlux
import NLS.KdV.HillClosedCurveDirections
import NLS.KdV.HillDiscriminantQuadraticSystem

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ComplexAnalysis
namespace NLS.KdV

/-- Physical spatial data for KdV: q,q_x,q_xx,q_xxx, actual a.e.
derivatives, and periodic boundary values. No spectral condition occurs. -/
structure PeriodicKdVJet where
  value : Curve ℂ
  first : Curve ℂ
  second : Curve ℂ
  third : Curve ℂ
  ac_value : AbsolutelyContinuousOnInterval (extend value) 0 1
  ac_first : AbsolutelyContinuousOnInterval (extend first) 0 1
  ac_second : AbsolutelyContinuousOnInterval (extend second) 0 1
  derivatives : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
    HasDerivAt (extend value) (extend first x) x ∧
    HasDerivAt (extend first) (extend second x) x ∧
    HasDerivAt (extend second) (extend third x) x
  periodic_value : value ⟨1,by norm_num⟩ = value ⟨0,by norm_num⟩
  periodic_first : first ⟨1,by norm_num⟩ = first ⟨0,by norm_num⟩
  periodic_second : second ⟨1,by norm_num⟩ = second ⟨0,by norm_num⟩
  periodic_third : third ⟨1,by norm_num⟩ = third ⟨0,by norm_num⟩

namespace PeriodicKdVJet

def velocity (J : PeriodicKdVJet) : Curve ℂ := (6 : ℂ) • (J.value*J.first)-J.third

theorem velocity_periodic (J : PeriodicKdVJet) :
    J.velocity ⟨1,by norm_num⟩ = J.velocity ⟨0,by norm_num⟩ := by
  simp only [velocity,ContinuousMap.sub_apply,ContinuousMap.smul_apply,
    ContinuousMap.mul_apply,J.periodic_value,J.periodic_first,J.periodic_third]

def coefficients (J : PeriodicKdVJet) : WeightedCoeff SpectralWeight.one.toWeight 2 :=
  hillClosedCurveCoefficients J.value J.periodic_value.symm

def velocityCoefficients (J : PeriodicKdVJet) : WeightedCoeff SpectralWeight.one.toWeight 2 :=
  hillClosedCurveCoefficients J.velocity J.velocity_periodic.symm

/-- The KdV field has zero physical mean, by its local divergence form. -/
theorem velocity_mean_zero (J : PeriodicKdVJet) : J.velocityCoefficients.val 0 = 0 := by
  let F : ℝ → ℂ := (3 : ℂ) • (extend J.value*extend J.value)-extend J.second
  have hF : AbsolutelyContinuousOnInterval F 0 1 :=
    ((J.ac_value.smul J.ac_value).const_smul (3 : ℂ)).sub J.ac_second
  have hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt F (extend J.velocity x) x := by
    filter_upwards [J.derivatives] with x hx
    convert! ((hx.1.mul hx.1).const_mul (3 : ℂ)).sub hx.2.2 using 1
    dsimp only [velocity,NLS.LinearVolterra.extend,ContinuousMap.sub_apply,
      ContinuousMap.smul_apply,ContinuousMap.mul_apply,smul_eq_mul]
    ring
  have hper : F 1 = F 0 := by
    dsimp only [F,Pi.sub_apply,Pi.smul_apply,Pi.mul_apply,smul_eq_mul,NLS.LinearVolterra.extend]
    rw [projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num),
      projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num),J.periodic_value,J.periodic_second]
  have hh := (ae_restrict_iff' measurableSet_Icc).mp
    (by simpa only [restrict_Ioc_eq_restrict_Icc] using hd)
  have hFTC := integral_eq_sub_of_ac_of_ae_hasDerivAt hF
    ((continuous_extend J.velocity).intervalIntegrable 0 1)
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hh)
  rw [velocityCoefficients,hillClosedCurveCoefficients_zero]
  exact hFTC.trans (sub_eq_zero.mpr hper)

theorem representative_ae (J : PeriodicKdVJet) :
    hillL2ScalarRepresentative (SpectralWeight.one.toCoeff J.coefficients)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] extend J.value := by
  have hh := hillL2ScalarRepresentative_eq_continuous
    (closedUnitCurvePeriodTwo J.value J.periodic_value.symm)
  apply hh.trans
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  dsimp only [NLS.LinearVolterra.extend,hillUnitPotentialCurve,ContinuousMap.coe_mk]
  rw [projIcc_of_mem _ (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1.le,hx.2⟩)]
  change closedUnitCurvePeriodic J.value J.periodic_value.symm x = J.value ⟨x,hx.1.le,hx.2⟩
  simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1.le,hx.2⟩)] using
    closedUnitCurvePeriodic_eq J.value J.periodic_value.symm x hx

/-- The actual discriminant cotangent annihilates the physical KdV field. -/
theorem discriminant_stationary (J : PeriodicKdVJet) (z : ℂ) :
    hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff J.velocityCoefficients)
      (hillDiscriminantGradientCurve (SpectralWeight.one.toCoeff J.coefficients) z) = 0 := by
  let q := SpectralWeight.one.toCoeff J.coefficients
  let G := hillDiscriminantGradientCurve q z
  let H := hillDiscriminantGradientSpatialCurve q z
  let R := hillDiscriminantQuadraticMomentumCurve q z
  have hsys := ae_hasDerivAt_hillDiscriminantQuadraticSystem q z
  have hsysJ : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend G) (extend H x) x ∧
      HasDerivAt (extend H) (2*(extend J.value x-z^2)*extend G x+2*extend R x) x ∧
      HasDerivAt (extend R) ((extend J.value x-z^2)*extend H x) x := by
    filter_upwards [hsys,J.representative_ae] with x hx hy
    simpa only [q,hy] using hx
  have hga := absolutelyContinuousOnInterval_hillDiscriminantGradientCurve q z
  have hha := absolutelyContinuousOnInterval_hillDiscriminantQuadraticSystem q z
  have hgp := hillDiscriminantGradientCurve_endpoints q z
  have hhp := hillDiscriminantGradientSpatialCurve_endpoints q z
  have hrp := hillDiscriminantQuadraticMomentumCurve_endpoints q z
  have hi := integral_quadraticHill_KdV_eq_zero (z^2) J.value J.first J.second J.third G H R
    J.ac_value J.ac_first J.ac_second hga hha.1 hha.2 J.derivatives hsysJ
    (by
      intro f hf
      simp only [mem_insert_iff,mem_singleton_iff] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
      · exact J.periodic_value
      · exact J.periodic_first
      · exact J.periodic_second
      · exact hgp.2.trans hgp.1.symm
      · exact hhp.2.trans hhp.1.symm
      · exact hrp.2.trans hrp.1.symm)
  rw [velocityCoefficients,hillClosedCurveCoefficients_pairing,unitComplexCurvePairing_apply]
  change (∫ x in (0 : ℝ)..1,extend J.velocity x*extend G x) = 0
  have he : (fun x => extend J.velocity x*extend G x) =
      fun x => -(extend G x*(extend J.third x-6*extend J.value x*extend J.first x)) := by
    funext x
    dsimp only [velocity,NLS.LinearVolterra.extend,ContinuousMap.sub_apply,
      ContinuousMap.smul_apply,ContinuousMap.mul_apply,smul_eq_mul]
    ring
  rw [he,intervalIntegral.integral_neg,hi,neg_zero]

end PeriodicKdVJet
end NLS.KdV
