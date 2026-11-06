import NLS.ComplexAnalysis.RealGapDiscIsolation

/-! # A free-centered comparison circle inside the canonical real-gap circle

Small endpoint errors and large adjacent band lengths place the comparison
disc inside the midpoint disc with its quarter-band collar. Both circles
enclose the same cut, including when its endpoints coincide.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem real_gap_comparison_circle_nesting
    (e l a b u t : ℝ) (ht : 0 < t) (hab : a ≤ b)
    (ha : |a-e| ≤ t/8) (hb : |b-e| ≤ t/8)
    (hla : 8*t ≤ a-l) (hbu : 8*t ≤ u-b) :
    closedBall (e : ℂ) t ⊆ closedBall (((a+b)/2 : ℝ) : ℂ)
        ((b-a)/2+min (a-l) (u-b)/4) ∧
      segment ℝ (a : ℂ) (b : ℂ) ⊆ ball (e : ℂ) t := by
  have hd : 0 ≤ (b-a)/2 := by linarith
  have hη : 2*t ≤ min (a-l) (u-b)/4 := by
    have hm := le_min hla hbu
    linarith
  have hc : |(a+b)/2-e| ≤ t/8 := by
    have h₁ := abs_le.mp ha
    have h₂ := abs_le.mp hb
    apply abs_le.mpr
    constructor <;> linarith
  have hdist : dist (((a+b)/2 : ℝ) : ℂ) (e : ℂ) ≤ t/8 := by
    simpa only [dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hc
  constructor
  · intro z hz
    have hzt := mem_closedBall.mp hz
    have htri := dist_triangle z (e : ℂ) (((a+b)/2 : ℝ) : ℂ)
    have hdc : dist (e : ℂ) (((a+b)/2 : ℝ) : ℂ) ≤ t/8 := by
      simpa only [dist_comm] using hdist
    apply mem_closedBall.mpr
    linarith
  · apply (convex_ball _ _).segment_subset
    · have hlt : |a-e| < t := ha.trans_lt (by linarith)
      simpa only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hlt
    · have hlt : |b-e| < t := hb.trans_lt (by linarith)
      simpa only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hlt

end NLS.ComplexAnalysis
