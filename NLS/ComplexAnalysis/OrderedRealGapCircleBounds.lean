import NLS.ComplexAnalysis.RealCenteredPositiveDisc

/-! # Real-band crossings of an isolating circle

An enclosed real gap and two excluded neighboring endpoints put the
circle's two real crossings in the adjacent open spectral bands.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem ordered_real_gap_circle_bounds (c r l a b u : ℝ)
    (ha : (a : ℂ) ∈ ball (c : ℂ) r) (hb : (b : ℂ) ∈ ball (c : ℂ) r)
    (hl : (l : ℂ) ∉ closedBall (c : ℂ) r) (hu : (u : ℂ) ∉ closedBall (c : ℂ) r)
    (hla : l ≤ a) (hbu : b ≤ u) :
    c-r ∈ Ioo l a ∧ c+r ∈ Ioo b u := by
  have ha' : |a-c| < r := by
    simpa only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using ha
  have hb' : |b-c| < r := by
    simpa only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hb
  have hl' : r < |l-c| := by
    apply lt_of_not_ge
    simpa only [mem_closedBall,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hl
  have hu' : r < |u-c| := by
    apply lt_of_not_ge
    simpa only [mem_closedBall,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hu
  have hal := (abs_lt.mp ha').1
  have hau := (abs_lt.mp ha').2
  have hbl := (abs_lt.mp hb').1
  have hbu' := (abs_lt.mp hb').2
  have hlc : l-c ≤ 0 := by
    by_contra hn
    rw [abs_of_pos (lt_of_not_ge hn)] at hl'
    linarith
  have huc : 0 ≤ u-c := by
    by_contra hn
    rw [abs_of_neg (lt_of_not_ge hn)] at hu'
    linarith
  rw [abs_of_nonpos hlc] at hl'
  rw [abs_of_nonneg huc] at hu'
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

end NLS.ComplexAnalysis
