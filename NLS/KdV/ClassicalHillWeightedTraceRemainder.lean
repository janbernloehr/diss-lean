import NLS.KdV.ClassicalHillTraceFirstRemainder
import NLS.ComplexAnalysis.WeightedCosineDuhamelBounds

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

/-- The actual trace with its EXACT first mean term removed has quadratic
potential mass and the true exp(|Im z|)/|z|² bound. The smallness threshold
is independent of the imaginary part of the frequency. -/
theorem classicalHillDiscriminant_first_order_remainder_bound
    (q : Curve ℂ) (z : ℂ) (hz : z ≠ 0)
    (hsmall : classicalHillPotentialMass q / ‖z‖ ≤ 1/2) :
    ‖classicalHillDiscriminant q (z^2) - 2*cos z -
      sin z/z * (∫ s in (0:ℝ)..1, NLS.LinearVolterra.extend q s)‖ ≤
      4 * Real.exp |z.im| * (classicalHillPotentialMass q)^2 / ‖z‖^2 := by
  let M := classicalHillPotentialMass q
  have hc (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖classicalHillCosineStateError q z s‖ ≤ Real.exp (|z.im| * s) * (2*M/‖z‖) := by
    have hh := classicalHillFlow_position_free_error_weighted q z hz hsmall
      (1,0) (⟨s,hs⟩ : Icc (0:ℝ) 1)
    simpa only [classicalHillCosineStateError,mul_one,mul_zero,add_zero,norm_one,norm_zero,
      zero_div,one_mul] using hh
  have hs (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖classicalHillSineStateError q z s‖ ≤ Real.exp (|z.im| * s) * (2*M/‖z‖^2) := by
    calc
      _ = ‖(classicalHillFlow q (z^2) (0,1) s).1 -
          (cos (z*s)*0 + sin (z*s)/z*1)‖ := by
        simp only [classicalHillSineStateError,mul_zero,mul_one,zero_add]
      _ ≤ Real.exp (|z.im| * s) *
          (2*(‖(0:ℂ)‖ + ‖(1:ℂ)‖/‖z‖)*M/‖z‖) :=
        classicalHillFlow_position_free_error_weighted q z hz hsmall (0,1) ⟨s,hs⟩
      _ = _ := by simp only [norm_zero,norm_one,zero_add]; ring
  have hiC := norm_sine_duhamel_integral_weighted_le (NLS.LinearVolterra.extend q)
    (classicalHillCosineStateError q z) z |z.im| (2*M/‖z‖) 1 (continuous_extend q) le_rfl (by norm_num) hc
  have hiS := norm_cosine_duhamel_integral_le_weighted (NLS.LinearVolterra.extend q)
    (classicalHillSineStateError q z) z (2*M/‖z‖^2) 1 (continuous_extend q) (by norm_num) hs
  rw [classicalHillDiscriminant_first_order_remainder q z hz]
  apply (norm_add_le _ _).trans
  apply (add_le_add hiC hiS).trans_eq
  change (Real.exp (|z.im| * 1)/‖z‖*(2*M/‖z‖))*M +
    (Real.exp (|z.im| * 1)*(2*M/‖z‖^2))*M = _
  rw [mul_one]
  dsimp only [M]
  ring

end NLS.KdV
