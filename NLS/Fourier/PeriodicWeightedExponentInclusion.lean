import NLS.Fourier.PeriodicExponentInclusion

/-! Exponent inclusion with an arbitrary admissible original weight,
preserving the entire physical distribution and the exact norm bound. -/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

def weightedExponentInclusion (w : Weight) (hw : w.HasTemperedInverse) (hpq : p ≤ q) :
    PeriodicFourierLebesgue L w p →L[ℂ] PeriodicFourierLebesgue L w q :=
  (coefficientsIsometry w q hw).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.exponentInclusion w hpq).comp
      (coefficientsIsometry w p hw).toContinuousLinearEquiv.toContinuousLinearMap)

theorem weightedExponentInclusion_coefficients (w : Weight) (hw : w.HasTemperedInverse)
    (hpq : p ≤ q) (f : PeriodicFourierLebesgue L w p) :
    coefficientsIsometry w q hw (weightedExponentInclusion w hw hpq f) =
      WeightedCoeff.exponentInclusion w hpq (coefficientsIsometry w p hw f) :=
  (coefficientsIsometry w q hw).apply_symm_apply _

theorem weightedExponentInclusion_val (w : Weight) (hw : w.HasTemperedInverse)
    (hpq : p ≤ q) (f : PeriodicFourierLebesgue L w p) :
    (weightedExponentInclusion w hw hpq f).val = f.val := by
  apply Distribution.ext_coefficients
  intro k
  have h := congrArg (fun a : WeightedCoeff w q => a.val k)
    (weightedExponentInclusion_coefficients w hw hpq f)
  rw [WeightedCoeff.exponentInclusion_apply] at h
  change (weightedExponentInclusion w hw hpq f).val (mode (-k)) = f.val (mode (-k)) at h
  exact h

theorem norm_weightedExponentInclusion_le (w : Weight) (hw : w.HasTemperedInverse)
    (hpq : p ≤ q) (f : PeriodicFourierLebesgue L w p) :
    ‖weightedExponentInclusion w hw hpq f‖ ≤ ‖f‖ := by
  have h := WeightedCoeff.norm_exponentInclusion_le w hpq (coefficientsIsometry w p hw f)
  rw [← weightedExponentInclusion_coefficients w hw hpq f] at h
  simpa only [LinearIsometryEquiv.norm_map] using h

end NLS.Fourier.PeriodicFourierLebesgue
