import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Interpolating discs around a complex line segment

If both endpoint discs strictly contain a line segment, then linear
interpolation of their centers and radii still strictly contains the
whole segment. Consequently every circle in the interpolation avoids
the segment. This is the geometric input for deforming inverse-root
contours without crossing their branch cuts.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

/-- A point interior to two discs remains interior when both center and
radius are linearly interpolated. -/
theorem mem_ball_interpolated_center_radius
    (x c₀ c₁ : ℂ) (r₀ r₁ s : ℝ)
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1)
    (hx₀ : x ∈ ball c₀ r₀) (hx₁ : x ∈ ball c₁ r₁) :
    x ∈ ball ((1-s) • c₀ + s • c₁) ((1-s)*r₀+s*r₁) := by
  have h₀ : ‖x-c₀‖ < r₀ := by simpa only [mem_ball, dist_eq_norm] using hx₀
  have h₁ : ‖x-c₁‖ < r₁ := by simpa only [mem_ball, dist_eq_norm] using hx₁
  have hs₀' : 0 ≤ 1-s := by linarith
  have heq : x-((1-s) • c₀+s • c₁) = (1-s) • (x-c₀)+s • (x-c₁) := by
    module
  have hnorm : ‖x-((1-s) • c₀+s • c₁)‖ ≤
      (1-s)*‖x-c₀‖+s*‖x-c₁‖ := by
    rw [heq]
    calc
      ‖(1-s) • (x-c₀)+s • (x-c₁)‖ ≤
          ‖(1-s) • (x-c₀)‖+‖s • (x-c₁)‖ := norm_add_le _ _
      _ = (1-s)*‖x-c₀‖+s*‖x-c₁‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hs₀', abs_of_nonneg hs₀]
  have hstrict : (1-s)*‖x-c₀‖+s*‖x-c₁‖ < (1-s)*r₀+s*r₁ := by
    by_cases hs : s = 0
    · subst s
      simpa using h₀
    · have hsp : 0 < s := lt_of_le_of_ne hs₀ (Ne.symm hs)
      have hleft := mul_le_mul_of_nonneg_left h₀.le hs₀'
      have hright := mul_lt_mul_of_pos_left h₁ hsp
      linarith
  simpa only [mem_ball, dist_eq_norm] using lt_of_le_of_lt hnorm hstrict

/-- The straight segment remains strictly inside every interpolated
disc when its endpoints lie in both original discs. -/
theorem segment_subset_interpolated_ball
    (a b c₀ c₁ : ℂ) (r₀ r₁ s : ℝ)
    (hs : s ∈ Set.Icc (0:ℝ) 1)
    (ha₀ : a ∈ ball c₀ r₀) (hb₀ : b ∈ ball c₀ r₀)
    (ha₁ : a ∈ ball c₁ r₁) (hb₁ : b ∈ ball c₁ r₁) :
    segment ℝ a b ⊆
      ball ((1-s) • c₀+s • c₁) ((1-s)*r₀+s*r₁) := by
  intro x hx
  have hx₀ : x ∈ ball c₀ r₀ :=
    (convex_ball c₀ r₀).segment_subset ha₀ hb₀ hx
  have hx₁ : x ∈ ball c₁ r₁ :=
    (convex_ball c₁ r₁).segment_subset ha₁ hb₁ hx
  exact mem_ball_interpolated_center_radius x c₀ c₁ r₀ r₁ s hs.1 hs.2 hx₀ hx₁

/-- Every interpolated circle avoids the enclosed segment. -/
theorem interpolated_sphere_disjoint_segment
    (a b c₀ c₁ : ℂ) (r₀ r₁ s : ℝ)
    (hs : s ∈ Set.Icc (0:ℝ) 1)
    (ha₀ : a ∈ ball c₀ r₀) (hb₀ : b ∈ ball c₀ r₀)
    (ha₁ : a ∈ ball c₁ r₁) (hb₁ : b ∈ ball c₁ r₁) :
    Disjoint (sphere ((1-s) • c₀+s • c₁) ((1-s)*r₀+s*r₁))
      (segment ℝ a b) := by
  have hsub := segment_subset_interpolated_ball
    a b c₀ c₁ r₀ r₁ s hs ha₀ hb₀ ha₁ hb₁
  apply Set.disjoint_left.mpr
  intro x hx hseg
  exact (sphere_disjoint_ball.le_bot ⟨hx, hsub hseg⟩)

end NLS.ComplexAnalysis
