import NLS.KdV.ClassicalHillSmallPotential
import NLS.KdV.HillDiscriminantComparison
import NLS.ComplexAnalysis.UnitIntervalNormEnergy

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.Fourier NLS.LinearVolterra NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV



theorem classicalHillPotentialMass_continuous_bound (Q : C(AddCircle (2 : ℝ), ℂ)) :
    classicalHillPotentialMass (hillUnitPotentialCurve Q) ≤
      2*‖SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)‖ := by
  let f : ℝ → ℂ := fun t => Q (t : AddCircle (2 : ℝ))
  have hf : Continuous f := Q.continuous.comp (by fun_prop)
  have hmem := memLp_two_interval hf 0 2 (by norm_num)
  have heq : periodTwoL2Coefficients f hmem = SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) := by
    ext k
    rw [periodTwoL2Coefficients_apply,SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
    exact periodTwoCoefficient_circle Q k
  have he := norm_sq_periodTwoL2Coefficients f hmem
  rw [heq] at he
  have hpart := intervalIntegral.integral_mono_interval (μ := volume)
    (a := (0 : ℝ)) (b := 1) (c := 0) (d := 2) le_rfl (by norm_num) (by norm_num)
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖f t‖))
    ((hf.norm.pow 2).intervalIntegrable 0 2)
  have hmass : classicalHillPotentialMass (hillUnitPotentialCurve Q) = ∫ t in (0 : ℝ)..1, ‖f t‖ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ ht,hillUnitPotentialCurve,ContinuousMap.coe_mk,f]
  rw [hmass]
  have hcs := integral_norm_sq_unit_le_energy f hf
  have hn : 0 ≤ ∫ t in (0 : ℝ)..1,‖f t‖ := intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)
  nlinarith [norm_nonneg (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))]

end NLS.KdV
