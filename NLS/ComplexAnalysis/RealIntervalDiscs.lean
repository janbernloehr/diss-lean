import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Complex discs around separated real intervals

Midpoint-centered discs containing real intervals provide the central
isolating neighborhoods in Section 10. Explicit margin inequalities keep
discs for separated intervals disjoint.
-/

namespace NLS.ComplexAnalysis
open Set Metric Complex

/-- A real point in an interval lies strictly inside its midpoint-centered
complex disc when the radius includes any positive extra margin. -/
theorem real_mem_midpoint_disc_of_mem_Icc {l r ε : ℝ}
    (hε : 0 < ε) {z : ℂ} (him : z.im = 0) (hz : z.re ∈ Icc l r) :
    z ∈ ball (((l+r)/2 : ℝ) : ℂ) ((r-l)/2+ε) := by
  have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him)
  rw [he, mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hleft : -((r-l)/2) ≤ z.re-(l+r)/2 := by linarith [hz.1]
  have hright : z.re-(l+r)/2 ≤ (r-l)/2 := by linarith [hz.2]
  rw [abs_lt]
  constructor <;> linarith

/-- Midpoint discs around separated real intervals are disjoint when their
extra margins sum to at most the gap between the intervals. -/
theorem midpoint_discs_disjoint_of_gap
    {l₁ r₁ l₂ r₂ ε₁ ε₂ : ℝ}
    (h₁ : l₁ ≤ r₁) (h₂ : l₂ ≤ r₂)
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hgap : ε₁+ε₂ ≤ l₂-r₁) :
    Disjoint
      (ball (((l₁+r₁)/2 : ℝ) : ℂ) ((r₁-l₁)/2+ε₁))
      (ball (((l₂+r₂)/2 : ℝ) : ℂ) ((r₂-l₂)/2+ε₂)) := by
  apply ball_disjoint_ball
  have hc : dist (((l₁+r₁)/2 : ℝ) : ℂ) (((l₂+r₂)/2 : ℝ) : ℂ) =
      |(l₁+r₁)/2-(l₂+r₂)/2| := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hc]
  have horder : (l₁+r₁)/2 ≤ (l₂+r₂)/2 := by linarith
  rw [abs_of_nonpos (sub_nonpos.mpr horder)]
  linarith

/-- A midpoint disc lies to the left of a point-centered disc when the
combined margins fit between the interval and the point. -/
theorem midpoint_disc_disjoint_right_point_disc
    {l r c ε ρ : ℝ} (hlr : l ≤ r) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (hgap : ε + ρ ≤ c-r) :
    Disjoint (ball (((l+r)/2 : ℝ) : ℂ) ((r-l)/2+ε))
      (ball (c : ℂ) ρ) := by
  simpa using midpoint_discs_disjoint_of_gap hlr le_rfl hε hρ hgap

/-- A point-centered disc lies to the left of a midpoint disc when the
combined margins fit between the point and the interval. -/
theorem point_disc_disjoint_right_midpoint_disc
    {l r c ε ρ : ℝ} (hlr : l ≤ r) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (hgap : ρ + ε ≤ l-c) :
    Disjoint (ball (c : ℂ) ρ)
      (ball (((l+r)/2 : ℝ) : ℂ) ((r-l)/2+ε)) := by
  simpa using midpoint_discs_disjoint_of_gap le_rfl hlr hρ hε hgap

end NLS.ComplexAnalysis
