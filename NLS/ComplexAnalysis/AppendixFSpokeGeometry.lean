import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Separation of the endpoint spokes in the proof of F.2 -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

/-- Opposite real projections separate the two segments away from their common endpoint. -/
theorem appendixF_opposite_segments_avoid (l r ν g : ℂ)
    (hr : 0 < ((r-l)/g).re) (hν : ((ν-l)/g).re < 0)
    (z : ℂ) (hz : z ∈ segment ℝ l ν) (hzl : z ≠ l) : z ∉ segment ℝ l r := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  have ht0 : 0 < t := by
    by_contra hn
    have hzero : t = 0 := le_antisymm (not_lt.mp hn) ht.1
    simp [hzero] at hzl
  intro hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨s,hs,he⟩ := hz
  have hproj (a : ℂ) (u : ℝ) :
      ((AffineMap.lineMap l a u-l)/g).re = u*((a-l)/g).re := by
    have h : (AffineMap.lineMap l a u-l)/g = (u:ℂ)*((a-l)/g) := by
      simp only [AffineMap.lineMap_apply_module,Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one]
      ring
    rw [h,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have he' := congrArg (fun a : ℂ => ((a-l)/g).re) he
  rw [hproj,hproj] at he'
  have hp := mul_neg_of_pos_of_neg ht0 hν
  have hnonneg := mul_nonneg hs.1 hr.le
  linarith

/-- The quarter-gap and quarter-spoke tolerances keep the source's straight spoke off the gap. -/
theorem appendixF_perturbed_spoke_avoids_gap (l₀ r₀ l r : ℂ) (σ : ℝ)
    (hσ : 0 < σ) (hg : r₀-l₀ ≠ 0)
    (hl : ‖(l-l₀)/(r₀-l₀)‖ < min (1/4) (σ/4))
    (hr : ‖(r-r₀)/(r₀-l₀)‖ < 1/4)
    (z : ℂ) (hz : z ∈ segment ℝ l (l₀-(σ:ℂ)*(r₀-l₀))) (hzl : z ≠ l) :
    z ∉ segment ℝ l r := by
  apply appendixF_opposite_segments_avoid l r (l₀-(σ:ℂ)*(r₀-l₀)) (r₀-l₀) ?_ ?_ z hz hzl
  · have he : (r-l)/(r₀-l₀) = 1+(r-r₀)/(r₀-l₀)-(l-l₀)/(r₀-l₀) := by
      field_simp
      ring
    rw [he,Complex.sub_re,Complex.add_re,Complex.one_re]
    have hleft := Complex.re_le_norm ((l-l₀)/(r₀-l₀))
    have hright := (abs_le.mp (Complex.abs_re_le_norm ((r-r₀)/(r₀-l₀)))).1
    have hquarter := lt_of_lt_of_le hl (min_le_left _ _)
    linarith
  · have he : ((l₀-(σ:ℂ)*(r₀-l₀))-l)/(r₀-l₀) = -(σ:ℂ)-(l-l₀)/(r₀-l₀) := by
      field_simp
      ring
    rw [he,Complex.sub_re,Complex.neg_re,Complex.ofReal_re]
    have hleft := (abs_le.mp (Complex.abs_re_le_norm ((l-l₀)/(r₀-l₀)))).1
    have hquarter := lt_of_lt_of_le hl (min_le_right _ _)
    linarith

/-- The perturbed spoke stays in the original closed isolating disc and avoids the selected gap. -/
theorem appendixF_perturbed_spoke_in_disc (l₀ r₀ l r c : ℂ) (R σ : ℝ)
    (hσ : 0 < σ) (hg : r₀-l₀ ≠ 0)
    (hl : ‖(l-l₀)/(r₀-l₀)‖ < min (1/4) (σ/4))
    (hr : ‖(r-r₀)/(r₀-l₀)‖ < 1/4)
    (hlB : l ∈ Metric.closedBall c R)
    (hνB : l₀-(σ:ℂ)*(r₀-l₀) ∈ Metric.closedBall c R) :
    segment ℝ l (l₀-(σ:ℂ)*(r₀-l₀)) \ {l} ⊆
      Metric.closedBall c R \ segment ℝ l r := by
  intro z hz
  exact ⟨(convex_closedBall c R).segment_subset hlB hνB hz.1,
    appendixF_perturbed_spoke_avoids_gap l₀ r₀ l r σ hσ hg hl hr z hz.1
      (by simpa only [mem_singleton_iff] using hz.2)⟩

end NLS.ComplexAnalysis
