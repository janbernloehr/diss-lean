import NLS.ZakharovShabat.SourceStandardRootGapSidePositive

/-!
# Standard-root boundary values on the negative half of a real gap

Reflection about the midpoint exchanges the two sides of the positive
interior half and reverses the normalized root. This gives the real-gap
specialization of equation (2.12) for `-1 < t < 0`.
-/

noncomputable section
open Complex Filter
open scoped Topology

namespace NLS.ZakharovShabat

/-- Equation (2.12) on the negative half of a gap, approached from above. -/
theorem normalizedStandardRoot_tendsto_gap_upper_neg (τ : ℂ) (d t : ℝ)
    (hd : 0 < d) (ht : -1 < t) (ht0 : t < 0) :
    Tendsto (fun ε : ℝ =>
      normalizedStandardRoot τ ((2*(d:ℂ))^2)
        (τ+(d:ℂ)*((t:ℂ)+(ε:ℂ)*I)))
      (𝓝[>] (0:ℝ))
      (𝓝 (-(d:ℂ)*I*(Real.sqrt (1-t^2):ℂ))) := by
  have hs : 0 < -t := by linarith
  have hs1 : -t < 1 := by linarith
  have h := normalizedStandardRoot_tendsto_gap_lower_pos τ d (-t) hd hs hs1
  have hneg := h.neg
  have heq : (fun ε : ℝ =>
      normalizedStandardRoot τ ((2*(d:ℂ))^2)
        (τ+(d:ℂ)*((t:ℂ)+(ε:ℂ)*I))) =
      (fun ε : ℝ =>
        -normalizedStandardRoot τ ((2*(d:ℂ))^2)
          (τ+(d:ℂ)*(((-t:ℝ):ℂ)-(ε:ℂ)*I))) := by
    funext ε
    have hz : τ+(d:ℂ)*((t:ℂ)+(ε:ℂ)*I) =
        2*τ-(τ+(d:ℂ)*(((-t:ℝ):ℂ)-(ε:ℂ)*I)) := by
      push_cast
      ring
    rw [hz, normalizedStandardRoot_reflect]
  rw [heq]
  simpa only [neg_sq, neg_mul, neg_neg] using hneg

/-- Equation (2.12) on the negative half of a gap, approached from below. -/
theorem normalizedStandardRoot_tendsto_gap_lower_neg (τ : ℂ) (d t : ℝ)
    (hd : 0 < d) (ht : -1 < t) (ht0 : t < 0) :
    Tendsto (fun ε : ℝ =>
      normalizedStandardRoot τ ((2*(d:ℂ))^2)
        (τ+(d:ℂ)*((t:ℂ)-(ε:ℂ)*I)))
      (𝓝[>] (0:ℝ))
      (𝓝 ((d:ℂ)*I*(Real.sqrt (1-t^2):ℂ))) := by
  have hs : 0 < -t := by linarith
  have hs1 : -t < 1 := by linarith
  have h := normalizedStandardRoot_tendsto_gap_upper_pos τ d (-t) hd hs hs1
  have hneg := h.neg
  have heq : (fun ε : ℝ =>
      normalizedStandardRoot τ ((2*(d:ℂ))^2)
        (τ+(d:ℂ)*((t:ℂ)-(ε:ℂ)*I))) =
      (fun ε : ℝ =>
        -normalizedStandardRoot τ ((2*(d:ℂ))^2)
          (τ+(d:ℂ)*(((-t:ℝ):ℂ)+(ε:ℂ)*I))) := by
    funext ε
    have hz : τ+(d:ℂ)*((t:ℂ)-(ε:ℂ)*I) =
        2*τ-(τ+(d:ℂ)*(((-t:ℝ):ℂ)+(ε:ℂ)*I)) := by
      push_cast
      ring
    rw [hz, normalizedStandardRoot_reflect]
  rw [heq]
  simpa only [neg_sq, neg_mul, neg_neg] using hneg

end NLS.ZakharovShabat
