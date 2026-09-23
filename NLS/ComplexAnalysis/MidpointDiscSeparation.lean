import NLS.ComplexAnalysis.RealIntervalDiscs

/-!
# Positive distance between midpoint discs with a strict gap

When the right interval starts beyond the left interval's endpoint plus
the two disc margins and a positive remainder, every pair of points in
the discs is separated by that remainder.
-/

namespace NLS.ComplexAnalysis
open Set Metric Complex

/-- A quantitative pointwise separation of two complex midpoint discs. -/
theorem midpoint_discs_pointwise_separation
    {l₁ r₁ l₂ r₂ ε₁ ε₂ δ : ℝ}
    (h₁ : l₁ ≤ r₁) (h₂ : l₂ ≤ r₂)
    (hδ : 0 ≤ δ) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hgap : δ + ε₁ + ε₂ ≤ l₂-r₁)
    {z w : ℂ}
    (hz : z ∈ ball (((l₁+r₁)/2 : ℝ) : ℂ) ((r₁-l₁)/2+ε₁))
    (hw : w ∈ ball (((l₂+r₂)/2 : ℝ) : ℂ) ((r₂-l₂)/2+ε₂)) :
    δ ≤ dist z w := by
  have hcent : dist (((l₁+r₁)/2 : ℝ) : ℂ) (((l₂+r₂)/2 : ℝ) : ℂ) =
      (l₂+r₂)/2-(l₁+r₁)/2 := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonpos]
    · ring
    · linarith
  have hz' : dist (((l₁+r₁)/2 : ℝ) : ℂ) z < (r₁-l₁)/2+ε₁ := by
    simpa only [mem_ball, dist_comm] using hz
  have hw' : dist w (((l₂+r₂)/2 : ℝ) : ℂ) < (r₂-l₂)/2+ε₂ := by
    simpa only [mem_ball, dist_comm] using hw
  have htri := dist_triangle4 (((l₁+r₁)/2 : ℝ) : ℂ) z w (((l₂+r₂)/2 : ℝ) : ℂ)
  rw [hcent] at htri
  linarith

end NLS.ComplexAnalysis
