import NLS.ComplexAnalysis.NestedCircleHomotopy
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Comparing real-centered circles

Disjoint disks with real centers have disjoint real projections. A point
lying on the same side of two such projections cannot meet the affine
homotopy of the circles, even when neither disk contains the other.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

theorem re_bounds_of_mem_realCenteredBall {a r : ℝ} {z : ℂ}
    (hz : z ∈ ball (a : ℂ) r) : a-r < z.re ∧ z.re < a+r := by
  have hn : ‖z-(a : ℂ)‖ < r := by simpa only [mem_ball,dist_eq_norm] using hz
  have hab : |z.re-a| < r := lt_of_le_of_lt (by
    simpa only [sub_re,ofReal_re] using abs_re_le_norm (z-(a : ℂ))) hn
  obtain ⟨hl,hu⟩ := abs_lt.mp hab
  constructor <;> linarith

theorem re_bounds_of_mem_realCenteredClosedBall {a r : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (a : ℂ) r) : a-r ≤ z.re ∧ z.re ≤ a+r := by
  have hn : ‖z-(a : ℂ)‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hab : |z.re-a| ≤ r := le_trans (by
    simpa only [sub_re,ofReal_re] using abs_re_le_norm (z-(a : ℂ))) hn
  obtain ⟨hl,hu⟩ := abs_le.mp hab
  constructor <;> linarith

/-- The real projection of a disjoint real-centered disk lies strictly
outside the closed real projection of the selected disk. -/
theorem re_separated_of_disjoint_realCenteredBalls {a b r s : ℝ} {w : ℂ}
    (hr : 0 < r) (hs : 0 < s)
    (hd : Disjoint (ball (a : ℂ) r) (ball (b : ℂ) s))
    (hw : w ∈ ball (b : ℂ) s) : w.re < a-r ∨ a+r < w.re := by
  have hdist : r+s ≤ |a-b| := by
    simpa only [dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using
      (disjoint_ball_ball_iff hr hs).mp hd
  obtain ⟨hl,hu⟩ := re_bounds_of_mem_realCenteredBall hw
  rcases le_total b a with hba | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)] at hdist
    exact Or.inl (by linarith)
  · rw [abs_of_nonpos (sub_nonpos.mpr hab)] at hdist
    exact Or.inr (by linarith)

/-- Overlapping selected disks force a point outside both real projections
to lie on the same side of both. -/
theorem re_sameSide_of_mem_both_realCenteredBalls {a₀ a₁ r₀ r₁ : ℝ} {v w : ℂ}
    (hv₀ : v ∈ ball (a₀ : ℂ) r₀) (hv₁ : v ∈ ball (a₁ : ℂ) r₁)
    (hw₀ : w.re < a₀-r₀ ∨ a₀+r₀ < w.re)
    (hw₁ : w.re < a₁-r₁ ∨ a₁+r₁ < w.re) :
    (w.re < a₀-r₀ ∧ w.re < a₁-r₁) ∨ (a₀+r₀ < w.re ∧ a₁+r₁ < w.re) := by
  obtain ⟨hl₀,hu₀⟩ := re_bounds_of_mem_realCenteredBall hv₀
  obtain ⟨hl₁,hu₁⟩ := re_bounds_of_mem_realCenteredBall hv₁
  rcases hw₀ with hw₀ | hw₀ <;> rcases hw₁ with hw₁ | hw₁
  · exact Or.inl ⟨hw₀,hw₁⟩
  · exfalso; linarith
  · exfalso; linarith
  · exact Or.inr ⟨hw₀,hw₁⟩

/-- No nesting assumption is needed when a point is on the same side of
both real-centered circles. -/
theorem affineCircleHomotopy_ne_of_re_sameSide
    (a₀ a₁ r₀ r₁ : ℝ) (w : ℂ) (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hw : (w.re < a₀-r₀ ∧ w.re < a₁-r₁) ∨
      (a₀+r₀ < w.re ∧ a₁+r₁ < w.re)) (s u : I) :
    (ContinuousMap.Homotopy.affine
      (circlePath (a₀ : ℂ) r₀ : C(I,ℂ))
      (circlePath (a₁ : ℂ) r₁ : C(I,ℂ))) (s,u) ≠ w := by
  rw [ContinuousMap.Homotopy.affine_apply]
  change AffineMap.lineMap (circleMap (a₀ : ℂ) r₀ ((2*Real.pi)*(u : ℝ)))
    (circleMap (a₁ : ℂ) r₁ ((2*Real.pi)*(u : ℝ))) (s : ℝ) ≠ w
  have hb₀ := re_bounds_of_mem_realCenteredClosedBall
    (circleMap_mem_closedBall (a₀ : ℂ) hr₀ ((2*Real.pi)*(u : ℝ)))
  have hb₁ := re_bounds_of_mem_realCenteredClosedBall
    (circleMap_mem_closedBall (a₁ : ℂ) hr₁ ((2*Real.pi)*(u : ℝ)))
  rcases hw with hw | hw
  · have h := (convex_halfSpace_re_gt w.re).lineMap_mem
      (lt_of_lt_of_le hw.1 hb₀.1) (lt_of_lt_of_le hw.2 hb₁.1) s.property
    intro he
    simp only [mem_ofPred_eq] at h
    rw [he] at h
    exact lt_irrefl _ h
  · have h := (convex_halfSpace_re_lt w.re).lineMap_mem
      (lt_of_le_of_lt hb₀.2 hw.1) (lt_of_le_of_lt hb₁.2 hw.2) s.property
    intro he
    simp only [mem_ofPred_eq] at h
    rw [he] at h
    exact lt_irrefl _ h

end NLS.ComplexAnalysis
