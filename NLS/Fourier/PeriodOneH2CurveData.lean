import NLS.Fourier.PeriodOneH2CurveLift
import NLS.Fourier.PeriodOneCurveSynthesis
import NLS.ZakharovShabat.SobolevPhysicalJets
import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian

/-! # Physical periodic H² curves in the native Miura cotangent spaces

The data record consists entirely of actual interval derivatives, L²
regularity and periodic traces. Its native coefficients are the literal
unit-period Fourier integrals; both H¹ representatives recover every
point of the original interval and retain the physical derivative symbol.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Fourier

structure PeriodOneH2CurveData where
  profile : Curve ℂ
  spatial : Curve ℂ
  second : ℝ → ℂ
  profile_ac : AbsolutelyContinuousOnInterval (extend profile) 0 1
  spatial_ac : AbsolutelyContinuousOnInterval (extend spatial) 0 1
  second_memLp : MemLp second 2 (volume.restrict (Ioc (0 : ℝ) 1))
  hasDeriv : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend profile) (extend spatial x) x
  hasSecondDeriv : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend spatial) (second x) x
  profile_periodic : profile ⟨1,by norm_num⟩ = profile ⟨0,by norm_num⟩
  spatial_periodic : spatial ⟨1,by norm_num⟩ = spatial ⟨0,by norm_num⟩

namespace PeriodOneH2CurveData

def native (D : PeriodOneH2CurveData) : ScalarSobolev 2 :=
  periodOneH2CurveCoefficients D.profile D.spatial D.second D.profile_ac D.spatial_ac D.second_memLp
    D.hasDeriv D.hasSecondDeriv D.profile_periodic D.spatial_periodic

theorem native_apply (D : PeriodOneH2CurveData) (n : ℤ) :
    D.native.val n = periodOneCoefficient (extend D.profile) n := rfl

theorem profile_endpoints (D : PeriodOneH2CurveData) : extend D.profile 1 = extend D.profile 0 := by
  simpa only [NLS.LinearVolterra.extend,
    projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num),
    projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num)] using D.profile_periodic

theorem spatial_endpoints (D : PeriodOneH2CurveData) : extend D.spatial 1 = extend D.spatial 0 := by
  simpa only [NLS.LinearVolterra.extend,
    projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num),
    projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num)] using D.spatial_periodic

def inclusion (D : PeriodOneH2CurveData) : ScalarDomain 2 :=
  hierarchySobolevToScalarDomain 2 (by omega) D.native

def derivative (D : PeriodOneH2CurveData) : ScalarDomain 2 :=
  hierarchySobolevToScalarDomain 1 le_rfl (hierarchySobolevDerivative 2 1 (by omega) D.native)

theorem inclusion_apply (D : PeriodOneH2CurveData) (n : ℤ) :
    (D.inclusion).val n = periodOneCoefficient (extend D.profile) n := by
  rw [inclusion,hierarchySobolevToScalarDomain_apply,D.native_apply]

theorem derivative_apply (D : PeriodOneH2CurveData) (n : ℤ) :
    (D.derivative).val n = periodOneCoefficient (extend D.spatial) n := by
  have h := periodOneCoefficient_of_ac_derivative D.profile_ac (memLp_unitCurve_extend 2 D.spatial)
    D.hasDeriv D.profile_endpoints n
  rw [← D.native_apply n] at h
  rw [derivative,hierarchySobolevToScalarDomain_apply,
    hierarchySobolevDerivative_apply]
  exact h.symm

theorem second_apply (D : PeriodOneH2CurveData) (n : ℤ) :
    periodOneDerivative (D.derivative) n = periodOneCoefficient D.second n := by
  rw [periodOneDerivative_apply,D.derivative_apply]
  exact (periodOneCoefficient_of_ac_derivative D.spatial_ac D.second_memLp
    D.hasSecondDeriv D.spatial_endpoints n).symm

theorem profile_recovery (D : PeriodOneH2CurveData) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    periodOneSobolevSynthesis (D.inclusion) (x : AddCircle (2 : ℝ)) =
      extend D.profile x :=
  periodOneSobolevSynthesis_eq_curve _ D.profile D.profile_periodic D.inclusion_apply hx

theorem spatial_recovery (D : PeriodOneH2CurveData) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    periodOneSobolevSynthesis (D.derivative) (x : AddCircle (2 : ℝ)) =
      extend D.spatial x :=
  periodOneSobolevSynthesis_eq_curve _ D.spatial D.spatial_periodic D.derivative_apply hx

end PeriodOneH2CurveData
end NLS.Fourier
