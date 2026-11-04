import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Circle integrability from a continuous upper sheet and reflection

The two closed semicircles have continuous parametrizations. Reflection
supplies the lower half, and the finite boundary discrepancies do not affect
interval integrability. No continuation across the intervening real cuts
or matching boundary values at the real crossings is required.
-/
noncomputable section
open Set Metric Complex MeasureTheory
open scoped Interval ComplexConjugate
namespace NLS.ComplexAnalysis

/-- Upper-half continuity and conjugate reflection off the real axis suffice for circle integrability, even if the two real crossings have different sheet values. -/
theorem circleIntegrable_of_continuous_upper_reflection (f : ℂ → ℂ)
    (hf : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hrf : ∀ z : ℂ, z.im < 0 → f z = conj (f (conj z))) (r : ℝ) (hr : 0 < r) :
    CircleIntegrable f 0 r := by
  have hu : ContinuousOn (fun t : ℝ => f (circleMap 0 r t)) (Icc 0 Real.pi) := by
    apply hf.comp (continuous_circleMap 0 r).continuousOn
    intro t ht
    change 0 ≤ (circleMap 0 r t).im
    rw [circleMap_zero_im]
    exact mul_nonneg hr.le (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2)
  have hl : ContinuousOn (fun t : ℝ => conj (f (conj (circleMap 0 r t)))) (Icc Real.pi (2*Real.pi)) := by
    apply continuous_star.comp_continuousOn
    apply hf.comp (continuous_star.comp (continuous_circleMap 0 r)).continuousOn
    intro t ht
    change 0 ≤ (conj (circleMap 0 r t)).im
    rw [conj_im,circleMap_zero_im]
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi
      (show 0 ≤ t-Real.pi by linarith [ht.1]) (show t-Real.pi ≤ Real.pi by linarith [ht.2])
    rw [Real.sin_sub_pi] at hs
    nlinarith
  have hlI : IntervalIntegrable (fun t : ℝ => f (circleMap 0 r t)) volume Real.pi (2*Real.pi) := by
    apply (hl.intervalIntegrable_of_Icc (by linarith [Real.pi_pos])).congr_uIoo
    intro t ht
    have hle : Real.pi ≤ 2*Real.pi := by linarith [Real.pi_pos]
    have ht' : Real.pi < t ∧ t < 2*Real.pi := by simpa only [uIoo_of_le hle,mem_Ioo] using ht
    symm
    apply hrf
    rw [circleMap_zero_im]
    have hs := Real.sin_pos_of_pos_of_lt_pi
      (show 0 < t-Real.pi by linarith [ht'.1]) (show t-Real.pi < Real.pi by linarith [ht'.2])
    rw [Real.sin_sub_pi] at hs
    exact mul_neg_of_pos_of_neg hr (by linarith)
  exact (hu.intervalIntegrable_of_Icc (by positivity)).trans hlI

end NLS.ComplexAnalysis
