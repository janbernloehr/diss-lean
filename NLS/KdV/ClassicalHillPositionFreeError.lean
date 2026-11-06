import NLS.KdV.ClassicalHillSmallPotential

/-! # Uniform first Volterra errors for the actual Hill position columns -/
noncomputable section
open Set Metric Complex MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

theorem classicalHillFlow_position_free_error_small (q : Curve ℂ) (z : ℂ) (hz : z ≠ 0)
    (H : ℝ) (hH : |z.im| ≤ H)
    (hsmall : Real.exp H/‖z‖*classicalHillPotentialMass q ≤ 1/2)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖(classicalHillFlow q (z^2) v t).1-
      (cos (z*t.val)*v.1+sin (z*t.val)/z*v.2)‖ ≤
      2*(Real.exp H)^2*classicalHillPotentialMass q/‖z‖*(‖v.1‖+‖v.2‖/‖z‖) := by
  rw [classicalHillFlow_sine_duhamel q z hz v t,add_sub_cancel_left]
  have h := norm_sine_duhamel_integral_le (NLS.LinearVolterra.extend q)
    (fun s => (classicalHillFlow q (z^2) v s).1) z H
    (2*Real.exp H*(‖v.1‖+‖v.2‖/‖z‖)) t.val (continuous_extend q) hH t.property (by
      intro s hs
      exact classicalHillFlow_position_bound_small q z hz H hH hsmall v
        ⟨s,hs.1,hs.2.trans t.property.2⟩)
  apply h.trans
  apply (mul_le_mul_of_nonneg_left (classicalHillPotentialMass_partial_le q t) (by positivity)).trans_eq
  ring

end NLS.KdV
