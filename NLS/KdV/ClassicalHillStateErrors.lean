import NLS.KdV.ClassicalHillSmallPotential

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The normalized scalar Volterra error at every spatial point and initial
state, retaining the inverse-frequency gain in the position component. -/
theorem classicalHillFlow_position_free_error_small_of_state_bounds (q : Curve ℂ) (z : ℂ) (hz : z≠0)
    (H : ℝ) (hH : |z.im|≤H)
    (hsmall : Real.exp H/‖z‖*classicalHillPotentialMass q≤1/2)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖(classicalHillFlow q (z^2) v t).1-
      (cos (z*t.val)*v.1+sin (z*t.val)/z*v.2)‖≤
        (2*(Real.exp H)^2/‖z‖)*(‖v.1‖+‖v.2‖/‖z‖)*classicalHillPotentialMass q := by
  rw [classicalHillFlow_sine_duhamel q z hz v t,add_sub_cancel_left]
  have hb (s : ℝ) (hs : s∈Icc (0 : ℝ) t.val) :
      ‖(classicalHillFlow q (z^2) v s).1‖≤2*Real.exp H*(‖v.1‖+‖v.2‖/‖z‖) :=
    classicalHillFlow_position_bound_small q z hz H hH hsmall v ⟨s,hs.1,hs.2.trans t.property.2⟩
  have hh := norm_sine_duhamel_integral_le (extend q)
    (fun s => (classicalHillFlow q (z^2) v s).1) z H
    (2*Real.exp H*(‖v.1‖+‖v.2‖/‖z‖)) t.val (continuous_extend q) hH t.property hb
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left (classicalHillPotentialMass_partial_le q t) (by positivity)).trans_eq
  ring

/-- The velocity Volterra error at every spatial point and initial state. -/
theorem classicalHillFlow_velocity_free_error_small (q : Curve ℂ) (z : ℂ) (hz : z≠0)
    (H : ℝ) (hH : |z.im|≤H)
    (hsmall : Real.exp H/‖z‖*classicalHillPotentialMass q≤1/2)
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖(classicalHillFlow q (z^2) v t).2-
      (-z*sin (z*t.val)*v.1+cos (z*t.val)*v.2)‖≤
        (2*(Real.exp H)^2)*(‖v.1‖+‖v.2‖/‖z‖)*classicalHillPotentialMass q := by
  rw [classicalHillFlow_cosine_duhamel q z v t,add_sub_cancel_left]
  have hb (s : ℝ) (hs : s∈Icc (0 : ℝ) t.val) :
      ‖(classicalHillFlow q (z^2) v s).1‖≤2*Real.exp H*(‖v.1‖+‖v.2‖/‖z‖) :=
    classicalHillFlow_position_bound_small q z hz H hH hsmall v ⟨s,hs.1,hs.2.trans t.property.2⟩
  have hh := norm_cosine_duhamel_integral_le (extend q)
    (fun s => (classicalHillFlow q (z^2) v s).1) z H
    (2*Real.exp H*(‖v.1‖+‖v.2‖/‖z‖)) t.val (continuous_extend q) hH t.property hb
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left (classicalHillPotentialMass_partial_le q t) (by positivity)).trans_eq
  ring

end NLS.KdV
