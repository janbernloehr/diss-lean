import NLS.KdV.HillFreeStateCurves
import NLS.KdV.HillDirichletSlope

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

/-- Exact free physical slope at the original squared frequency. -/
theorem hillL2DirichletSlope_free_sq (z : ℂ) (hz : z ≠ 0) :
    hillL2DirichletSlope 0 (z^2) = cos z := by
  rw [hillL2DirichletSlope_sq]
  change (hillL2FrequencyStateCurve 0 z (0,1) ⟨1,by norm_num⟩).2 = _
  rw [hillL2FrequencyStateCurve_free_sine z hz]
  simp only [ofReal_one,mul_one]

/-- The exact ENERGY derivative of the original free characteristic.
The factor 2*z is retained from the squared-frequency chain rule. -/
theorem hillL2DirichletCharacteristic_free_energy_deriv (z : ℂ) (hz : z ≠ 0) :
    deriv (hillL2DirichletCharacteristic 0) (z^2) = (z*cos z-sin z)/(2*z^3) := by
  have hd := ((analyticOnNhd_hillL2DirichletCharacteristic 0 (z^2) (mem_univ _)).differentiableAt.hasDerivAt).comp z
    ((hasDerivAt_id z).pow 2)
  have hs := (Complex.hasDerivAt_sin z).div (hasDerivAt_id z) hz
  have he : (fun w : ℂ => hillL2DirichletCharacteristic 0 (w^2)) =ᶠ[𝓝 z]
      (fun w => sin w/w) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact hillL2DirichletCharacteristic_free_sq w hw
  have hh := hd.unique (hs.congr_of_eventuallyEq he)
  simp only [id_eq,Nat.reduceSub,pow_one,mul_one] at hh
  field_simp [hz] at hh ⊢
  linear_combination hh

/-- The exact ENERGY derivative of the original free norming slope. -/
theorem hillL2DirichletSlope_free_energy_deriv (z : ℂ) (hz : z ≠ 0) :
    deriv (hillL2DirichletSlope 0) (z^2) = -sin z/(2*z) := by
  have hd := ((analyticOnNhd_hillL2DirichletSlope 0 (z^2) (mem_univ _)).differentiableAt.hasDerivAt).comp z
    ((hasDerivAt_id z).pow 2)
  have he : (fun w : ℂ => hillL2DirichletSlope 0 (w^2)) =ᶠ[𝓝 z] cos := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact hillL2DirichletSlope_free_sq w hw
  have hh := hd.unique ((Complex.hasDerivAt_cos z).congr_of_eventuallyEq he)
  simp only [id_eq,Nat.reduceSub,pow_one,mul_one] at hh
  field_simp [hz]
  linear_combination hh

end NLS.KdV
