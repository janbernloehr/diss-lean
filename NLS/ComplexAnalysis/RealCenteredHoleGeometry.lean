import NLS.ComplexAnalysis.RealGapDiscIsolation

/-! # Enclosure and separation of real-centered circular holes -/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem real_closedBall_subset_diameter_ball (a r l u : ℝ)
    (hl : l < a - r) (hu : a + r < u) :
    closedBall (a : ℂ) r ⊆ ball (((l + u) / 2 : ℝ) : ℂ) ((u - l) / 2) := by
  have hcenter : |a - (l + u) / 2| < (u - l) / 2 - r := by
    rw [abs_lt]
    constructor <;> linarith
  intro z hz
  have ht := dist_triangle z (a : ℂ) (((l + u) / 2 : ℝ) : ℂ)
  have hc : dist (a : ℂ) (((l + u) / 2 : ℝ) : ℂ) = |a - (l + u) / 2| := by
    rw [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
  rw [hc] at ht
  rw [mem_ball]
  linarith [mem_closedBall.mp hz]

theorem real_closedBalls_disjoint_of_separated (a r b s : ℝ) (hsep : a + r < b - s) :
    Disjoint (closedBall (a : ℂ) r) (closedBall (b : ℂ) s) := by
  apply disjoint_left.mpr
  intro z hza hzb
  have ha : |z.re - a| ≤ r := by
    have hn : ‖z - (a : ℂ)‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hza
    simpa only [sub_re, ofReal_re] using (abs_re_le_norm (z - (a : ℂ))).trans hn
  have hb : |z.re - b| ≤ s := by
    have hn : ‖z - (b : ℂ)‖ ≤ s := by simpa only [mem_closedBall, dist_eq_norm] using hzb
    simpa only [sub_re, ofReal_re] using (abs_re_le_norm (z - (b : ℂ))).trans hn
  linarith [(abs_le.mp ha).2, (abs_le.mp hb).1]

end NLS.ComplexAnalysis
