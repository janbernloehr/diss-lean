import NLS.KdV.ClassicalHillWeightedDirichletError

noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra
namespace NLS.KdV

/-- The actual position/free-position error at every physical time has
one true exponential factor and one inverse frequency, uniformly on L1
potential mass balls. The initial state is arbitrary. -/
theorem classicalHillFlow_position_free_error_weighted
    (q : Curve ℂ) (z : ℂ) (hz : z ≠ 0)
    (hsmall : classicalHillPotentialMass q / ‖z‖ ≤ 1/2)
    (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    ‖(classicalHillFlow q (z^2) v t).1 -
        (cos (z*t.val) * v.1 + sin (z*t.val)/z * v.2)‖ ≤
      Real.exp (|z.im| * t.val) *
        (2 * (‖v.1‖ + ‖v.2‖/‖z‖) * classicalHillPotentialMass q / ‖z‖) := by
  let B := ‖v.1‖ + ‖v.2‖/‖z‖
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  rw [classicalHillFlow_sine_duhamel q z hz v t,add_sub_cancel_left]
  have hu (s : ℝ) (hs : s ∈ Icc (0:ℝ) t.val) :
      ‖(classicalHillFlow q (z^2) v s).1‖ ≤ Real.exp (|z.im| * s) * (2*B) := by
    have hh := classicalHillFlow_position_bound_weighted q z hz hsmall v
      (⟨s,hs.1,hs.2.trans t.property.2⟩ : Icc (0:ℝ) 1)
    exact hh.trans_eq (by dsimp only [B]; ring)
  apply (norm_sine_duhamel_integral_le_weighted (NLS.LinearVolterra.extend q)
    (fun s => (classicalHillFlow q (z^2) v s).1) z (2*B) t.val
    (continuous_extend q) t.property.1 hu).trans
  apply (mul_le_mul_of_nonneg_left (classicalHillPotentialMass_partial_le q t)
    (by positivity : 0 ≤ Real.exp (|z.im| * t.val) / ‖z‖ * (2*B))).trans_eq
  dsimp only [B]
  ring

end NLS.KdV
