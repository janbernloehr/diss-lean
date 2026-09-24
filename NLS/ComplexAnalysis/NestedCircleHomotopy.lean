import NLS.ComplexAnalysis.AffineLoopHomotopy

/-!
# Affine homotopies between nested enclosing circles

Corresponding points on two circles have the same angular parameter.
Their affine interpolation is another circle, with interpolated center
and radius. If both endpoint circles enclose a point, every
intermediate circle continues to enclose that point.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- Affine interpolation of corresponding circle points is itself a
circle point at the interpolated center and radius. -/
theorem lineMap_circleMap_centers_radii
    (c₀ c₁ : ℂ) (r₀ r₁ θ t : ℝ) :
    AffineMap.lineMap (circleMap c₀ r₀ θ) (circleMap c₁ r₁ θ) t =
      circleMap (AffineMap.lineMap c₀ c₁ t)
        ((1-t)*r₀+t*r₁) θ := by
  simp [AffineMap.lineMap_apply, circleMap, vsub_eq_sub, vadd_eq_add]
  ring

/-- If a point is strictly inside both endpoint discs, the affine
homotopy of their circle paths never passes through it. -/
theorem affineCircleHomotopy_ne_of_mem_both_balls
    (c₀ c₁ w : ℂ) (r₀ r₁ : ℝ)
    (hw₀ : w ∈ ball c₀ r₀) (hw₁ : w ∈ ball c₁ r₁)
    (s u : I) :
    (ContinuousMap.Homotopy.affine
      (circlePath c₀ r₀ : C(I, ℂ))
      (circlePath c₁ r₁ : C(I, ℂ))) (s,u) ≠ w := by
  let t : ℝ := (s:ℝ)
  let a : ℝ := 1-t
  let b : ℝ := t
  let C : ℂ := AffineMap.lineMap c₀ c₁ t
  let ρ : ℝ := a*r₀+b*r₁
  have ha : 0 ≤ a := by dsimp [a,t]; linarith [s.property.2]
  have hb : 0 ≤ b := s.property.1
  have hab : a+b=1 := by dsimp [a,b]; ring
  have hr₀ : 0 < r₀ := lt_of_le_of_lt dist_nonneg (mem_ball.mp hw₀)
  have hr₁ : 0 < r₁ := lt_of_le_of_lt dist_nonneg (mem_ball.mp hw₁)
  have hρ : 0 < ρ := by
    by_cases ha0 : a = 0
    · have hbpos : 0 < b := by linarith
      dsimp [ρ]
      nlinarith [mul_pos hbpos hr₁]
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      dsimp [ρ]
      nlinarith [mul_pos hapos hr₀, mul_nonneg hb hr₁.le]
  have hC : C = a • c₀ + b • c₁ := by
    dsimp [C,a,b,t]
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    ring
  have hwC : w-C = a • (w-c₀) + b • (w-c₁) := by
    rw [hC]
    have habC : (a:ℂ)+(b:ℂ)=1 := by exact_mod_cast hab
    calc
      w - ((a:ℂ)*c₀+(b:ℂ)*c₁) =
          ((a:ℂ)+(b:ℂ))*w - ((a:ℂ)*c₀+(b:ℂ)*c₁) := by rw [habC]; ring
      _ = (a:ℂ)*(w-c₀)+(b:ℂ)*(w-c₁) := by ring
  have hnorm : ‖w-C‖ ≤ a*‖w-c₀‖+b*‖w-c₁‖ := by
    rw [hwC]
    calc
      ‖a • (w-c₀) + b • (w-c₁)‖ ≤
          ‖a • (w-c₀)‖ + ‖b • (w-c₁)‖ := norm_add_le _ _
      _ = a*‖w-c₀‖+b*‖w-c₁‖ := by
        simp [Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  have hd₀ : ‖w-c₀‖ < r₀ := by simpa [mem_ball, dist_eq_norm] using hw₀
  have hd₁ : ‖w-c₁‖ < r₁ := by simpa [mem_ball, dist_eq_norm] using hw₁
  have hgap₀ : 0 < r₀-‖w-c₀‖ := sub_pos.mpr hd₀
  have hgap₁ : 0 < r₁-‖w-c₁‖ := sub_pos.mpr hd₁
  have hweighted : a*‖w-c₀‖+b*‖w-c₁‖ < ρ := by
    have h0 : 0 ≤ a*(r₀-‖w-c₀‖) := mul_nonneg ha hgap₀.le
    have h1 : 0 ≤ b*(r₁-‖w-c₁‖) := mul_nonneg hb hgap₁.le
    by_cases ha0 : a = 0
    · have hbpos : 0 < b := by linarith
      have hp := mul_pos hbpos hgap₁
      dsimp [ρ]
      nlinarith
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hp := mul_pos hapos hgap₀
      dsimp [ρ]
      nlinarith
  have hwball : w ∈ ball C ρ := by
    rw [mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt hnorm hweighted
  have hcircle : (ContinuousMap.Homotopy.affine
      (circlePath c₀ r₀ : C(I, ℂ))
      (circlePath c₁ r₁ : C(I, ℂ))) (s,u) =
      circleMap C ρ ((2*Real.pi)*(u:ℝ)) := by
    rw [ContinuousMap.Homotopy.affine_apply]
    change AffineMap.lineMap
      (circleMap c₀ r₀ ((2*Real.pi)*(u:ℝ)))
      (circleMap c₁ r₁ ((2*Real.pi)*(u:ℝ))) t = _
    exact lineMap_circleMap_centers_radii c₀ c₁ r₀ r₁ _ t
  rw [hcircle]
  exact circleMap_ne_mem_ball hwball _

/-- If the first filled disc is inside the second, every point of
the affine circle homotopy stays in the second filled disc. -/
theorem affineCircleHomotopy_mem_outer_closedBall
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hnest : closedBall c₀ r₀ ⊆ closedBall c₁ r₁)
    (s u : I) :
    (ContinuousMap.Homotopy.affine
      (circlePath c₀ r₀ : C(I, ℂ))
      (circlePath c₁ r₁ : C(I, ℂ))) (s,u) ∈
      closedBall c₁ r₁ := by
  rw [ContinuousMap.Homotopy.affine_apply]
  change AffineMap.lineMap
    (circleMap c₀ r₀ ((2*Real.pi)*(u:ℝ)))
    (circleMap c₁ r₁ ((2*Real.pi)*(u:ℝ))) (s:ℝ) ∈ _
  exact (convex_closedBall c₁ r₁).lineMap_mem
    (hnest (circleMap_mem_closedBall c₀ hr₀ _))
    (circleMap_mem_closedBall c₁ hr₁ _) s.property

end NLS.ComplexAnalysis
