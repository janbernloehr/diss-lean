import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal

namespace NLS.ComplexAnalysis



theorem integral_norm_sq_unit_le_energy (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in (0 : ℝ)..1, ‖f t‖)^2 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 := by
  let A := ∫ t in (0 : ℝ)..1, ‖f t‖
  have hi : (∫ t in (0 : ℝ)..1,(‖f t‖-A)^2) =
      (∫ t in (0 : ℝ)..1,‖f t‖^2)-A^2 := by
    simp_rw [sub_sq]
    have hlin : IntervalIntegrable (fun t => 2*‖f t‖*A) volume 0 1 :=
      (show Continuous (fun t => 2*‖f t‖*A) by fun_prop).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add
      (f := fun t => ‖f t‖^2-2*‖f t‖*A) (g := fun _ => A^2)
      (((hf.norm.pow 2).intervalIntegrable 0 1).sub hlin) (continuous_const.intervalIntegrable 0 1),
      intervalIntegral.integral_sub (f := fun t => ‖f t‖^2) (g := fun t => 2*‖f t‖*A)
        ((hf.norm.pow 2).intervalIntegrable 0 1) hlin]
    simp only [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_const,sub_zero,smul_eq_mul,one_mul]
    dsimp only [A]
    ring
  have hn := intervalIntegral.integral_nonneg (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (fun t _ => sq_nonneg (‖f t‖-A))
  rw [hi] at hn
  linarith

end NLS.ComplexAnalysis
