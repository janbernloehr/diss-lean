import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ComplexAnalysis



theorem norm_normalized_circleIntegral_difference_le
    (f g : ℂ → ℂ) (c S : ℂ) (R B : ℝ) (hR : 0 ≤ R)
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R)
    (hbound : ∀ E ∈ sphere c R, ‖S*(f E-g E)‖ ≤ B) :
    ‖S*((2*(Real.pi : ℂ))⁻¹*(∮ E in C(c,R),f E)-
      (2*(Real.pi : ℂ))⁻¹*(∮ E in C(c,R),g E))‖ ≤ R*B := by
  have he : S*((2*(Real.pi : ℂ))⁻¹*(∮ E in C(c,R),f E)-
      (2*(Real.pi : ℂ))⁻¹*(∮ E in C(c,R),g E)) =
      (2*(Real.pi : ℂ))⁻¹*(∮ E in C(c,R),S*(f E-g E)) := by
    rw [circleIntegral.integral_const_mul,circleIntegral.integral_sub hf hg]
    ring
  rw [he,norm_mul,norm_inv,norm_mul,norm_ofNat,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  apply (mul_le_mul_of_nonneg_left (circleIntegral.norm_integral_le_of_norm_le_const hR hbound)
    (by positivity : 0 ≤ (2*Real.pi)⁻¹)).trans_eq
  field_simp

end NLS.ComplexAnalysis
