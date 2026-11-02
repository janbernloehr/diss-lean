import NLS.ComplexAnalysis.RealGapEllipse

/-! # Real gap discs meet the real axis only in the gap and its two bands -/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem ofReal_mem_ordered_segment (a b x : ℝ) (hab : a ≤ b) (hx : x ∈ Icc a b) :
    (x : ℂ) ∈ segment ℝ (a : ℂ) b := by
  have hm : x ∈ segment ℝ a b := by rwa [segment_eq_Icc hab]
  exact (image_segment ℝ Complex.ofRealCLM.toLinearMap.toAffineMap a b).subset
    (mem_image_of_mem _ hm)

theorem real_gap_disc_exterior_band (l a b u c R : ℝ) (hab : a ≤ b)
    (hl : l < c - R) (hu : c + R < u) (z : ℂ)
    (hz : z ∈ ball (c : ℂ) R \ segment ℝ (a : ℂ) b) :
    z.im ≠ 0 ∨ z.re ∈ Ioo l a ∨ z.re ∈ Ioo b u := by
  by_cases hi : z.im ≠ 0
  · exact Or.inl hi
  · have hzC : z = (z.re : ℂ) := by apply Complex.ext <;> simp [not_ne_iff.mp hi]
    have hdist : |z.re - c| < R := by
      have hd := mem_ball.mp hz.1
      rw [hzC, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs] at hd
      exact hd
    have hout : z.re ∉ Icc a b := by
      intro hx
      exact hz.2 (hzC.symm ▸ ofReal_mem_ordered_segment a b z.re hab hx)
    rcases lt_or_ge z.re a with ha | ha
    · exact Or.inr (Or.inl ⟨by linarith [(abs_lt.mp hdist).1], ha⟩)
    · have hb : b < z.re := lt_of_not_ge (fun hb => hout ⟨ha, hb⟩)
      exact Or.inr (Or.inr ⟨hb, by linarith [(abs_lt.mp hdist).2]⟩)

end NLS.ComplexAnalysis
