import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Continuous propagation of the normalized square-root branch

A positive base-point normalization on a preconnected domain controls the root error by its squared error.
-/

noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

/-- On the right half-plane, the error from one is bounded by the
corresponding squared error, without choosing a square-root function. -/
theorem norm_sub_one_le_sq_sub_one_of_re_nonneg (z : ℂ) (hz : 0 ≤ z.re) :
    ‖z-1‖ ≤ ‖z^2-1‖ := by
  have hsum : 1 ≤ ‖z+1‖ := by
    have h := re_le_norm (z+1)
    simp only [add_re,one_re] at h
    linarith
  calc
    _ ≤ ‖z-1‖*‖z+1‖ := le_mul_of_one_le_right (norm_nonneg _) hsum
    _ = ‖z^2-1‖ := by rw [← norm_mul]; congr 1; ring

/-- A square lying strictly within unit distance of one cannot come
from a purely imaginary number. -/
theorem re_ne_zero_of_norm_sq_sub_one_lt_one (z : ℂ) (hz : ‖z^2-1‖ < 1) : z.re ≠ 0 := by
  intro hre
  have h := neg_le_abs ((z^2-1).re)
  have hn := abs_re_le_norm (z^2-1)
  simp only [pow_two,mul_re,sub_re,one_re,hre,zero_mul] at h hn hz
  nlinarith [sq_nonneg z.im]

/-- Continuity on a connected domain propagates the positive square
root normalization from one base point, with a quantitative error bound. -/
theorem norm_sub_one_le_sq_sub_one_on_preconnected
    {E : Type*} [TopologicalSpace E] {U : Set E} (hU : IsPreconnected U)
    (f : E → ℂ) (hf : ContinuousOn f U) (a : E) (ha : a ∈ U) (hapos : 0 < (f a).re)
    (hsq : ∀ x ∈ U, ‖(f x)^2-1‖ < 1) :
    ∀ x ∈ U, ‖f x-1‖ ≤ ‖(f x)^2-1‖ := by
  intro x hx
  have hpos : 0 < (f x).re := by
    by_contra h
    obtain ⟨y,hy,hye⟩ := hU.intermediate_value hx ha (continuous_re.comp_continuousOn hf)
      (show (0:ℝ) ∈ Icc (f x).re (f a).re from ⟨le_of_not_gt h,hapos.le⟩)
    exact re_ne_zero_of_norm_sq_sub_one_lt_one (f y) (hsq y hy) hye
  exact norm_sub_one_le_sq_sub_one_of_re_nonneg (f x) hpos.le

end NLS.ComplexAnalysis
