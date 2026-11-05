import NLS.KdV.HillPeriodOneRestrictionInverse
import NLS.KdV.HillL2QuadraticTrace

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The exact quadratic action trace in the original even rough Hill source
space, with its original norm and physical action normalization. -/
theorem hasSum_hillRealGapIntegrals_quadratic_even_l2
    (q : RealPeriodOneHillPotential) (hmean : q.val.val 0=0) :
    HasSum (fun j : ℕ => (2*Real.pi*(j+1 : ℕ))*
      hillRealGapIntegral q.val q.property.1 q.property.2 (j+1) 0) ((1/2 : ℝ)*‖q.val‖^2) := by
  let p := hillPeriodOneRestriction SpectralWeight.one q.val
  have hp : IsRealHillPotential (SpectralWeight.one.doubleIndex.toCoeff p) :=
    hillPeriodOneRestriction_real SpectralWeight.one q.val q.property.2
  have hp0 : p.val 0=0 := by
    simpa only [p,hillPeriodOneRestriction_apply,mul_zero] using hmean
  have hunit : hillPeriodOneUnitPotential SpectralWeight.one p=q.val :=
    hillPeriodOneUnitPotential_restriction_even q.val q.property.1
  have hnorm : ‖p‖=‖q.val‖ := norm_hillPeriodOneRestriction_even SpectralWeight.one q.val q.property.1
  have hs := hasSum_hillNativeGapIntegrals_quadratic_l2 p hp hp0
  simpa only [hunit,hnorm] using hs

/-- Equality of all actual actions fixes the original rough source norm on
the mean-zero physical Hill space. -/
theorem hillSource_norm_eq_of_actions_eq
    (q p : RealPeriodOneHillPotential) (hq : q.val.val 0=0) (hp : p.val.val 0=0)
    (hI : ∀ k : ℕ, 1≤k → hillRealGapIntegral q.val q.property.1 q.property.2 k 0=
      hillRealGapIntegral p.val p.property.1 p.property.2 k 0) :
    ‖q.val‖=‖p.val‖ := by
  have hqsum := hasSum_hillRealGapIntegrals_quadratic_even_l2 q hq
  have hpsum := hasSum_hillRealGapIntegrals_quadratic_even_l2 p hp
  have he (j : ℕ) : (2*Real.pi*(j+1 : ℕ))*hillRealGapIntegral q.val q.property.1 q.property.2 (j+1) 0=
      (2*Real.pi*(j+1 : ℕ))*hillRealGapIntegral p.val p.property.1 p.property.2 (j+1) 0 := by
    rw [hI (j+1) (by omega)]
  have hsame : HasSum (fun j : ℕ => (2*Real.pi*(j+1 : ℕ))*
      hillRealGapIntegral p.val p.property.1 p.property.2 (j+1) 0) ((1/2 : ℝ)*‖q.val‖^2) := by
    simpa only [he] using hqsum
  have hh := hsame.unique hpsum
  nlinarith [norm_nonneg q.val,norm_nonneg p.val]

end NLS.KdV
