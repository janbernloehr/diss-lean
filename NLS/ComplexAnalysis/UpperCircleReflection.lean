import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Passing upper semicircle estimates to the whole circle by reflection -/

noncomputable section
open Set Metric Complex
open scoped ComplexConjugate
namespace NLS.ComplexAnalysis

theorem exists_upper_circleMap_parameter (z : ℂ) (R : ℝ) (hz : ‖z‖ = R) (hi : 0 ≤ z.im) :
    ∃ t : Icc (0 : ℝ) Real.pi, circleMap 0 R t = z := by
  refine ⟨⟨z.arg, ⟨arg_nonneg_iff.mpr hi, arg_le_pi z⟩⟩, ?_⟩
  rw [circleMap_zero, ← hz]
  exact norm_mul_exp_arg_mul_I z

theorem weighted_norm_bound_on_circle_of_upper_reflection (f : ℂ → ℂ) (R W B : ℝ)
    (hupper : ∀ z ∈ sphere (0 : ℂ) R, 0 ≤ z.im → W*‖f z‖ ≤ B)
    (hreflect : ∀ z : ℂ, z.im ≠ 0 → f (conj z) = conj (f z)) :
    ∀ z ∈ sphere (0 : ℂ) R, W*‖f z‖ ≤ B := by
  intro z hz
  by_cases hi : 0 ≤ z.im
  · exact hupper z hz hi
  have hcz : conj z ∈ sphere (0 : ℂ) R := by
    simpa only [mem_sphere_iff_norm, sub_zero, norm_conj] using hz
  have hh := hupper (conj z) hcz (by simp only [conj_im]; linarith)
  rw [hreflect z (by linarith), norm_conj] at hh
  exact hh

end NLS.ComplexAnalysis
