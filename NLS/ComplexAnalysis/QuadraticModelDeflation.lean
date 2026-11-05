import NLS.ComplexAnalysis.LocalTwoRootQuotient

/-! # Normalized deflation of a perturbed quadratic square

The error is measured before deflation. Both zeros, with repetition, lie
near the free center, and the normalized filled quotient is uniformly near
one on the entire disc. No division by the distance between the zeros occurs.
-/
noncomputable section
set_option autoImplicit false
open Complex Set Metric
namespace NLS.ComplexAnalysis

/-- The normalization corresponding to the free square
`-(z-c^2)^2/(4*c^2)`. -/
def normalizedQuadraticDeflation (c : ℝ) (f : ℂ → ℂ) (a b z : ℂ) : ℂ :=
  -4*(c : ℂ)^2*twoRootDeflation f a b z

/-- A zero of a uniformly close quadratic square lies near its free center. -/
theorem norm_root_sub_center_le_of_quadratic_error
    (c r δ : ℝ) (hc : 0 < c) (hr : 0 < r) (hδ : 0 ≤ δ)
    (f : ℂ → ℂ) (z : ℂ) (hz : f z = 0)
    (he : ‖f z- (-(z-(c : ℂ)^2)^2/(4*(c : ℂ)^2))‖ ≤ δ^2*r^2) :
    ‖z-(c : ℂ)^2‖ ≤ 2*c*r*δ := by
  have hden : ‖(4 : ℂ)*(c : ℂ)^2‖ = 4*c^2 := by simp [abs_of_pos hc]
  rw [hz, zero_sub, norm_neg, norm_div, norm_neg, norm_pow, hden] at he
  have hs := (div_le_iff₀ (by positivity : 0 < 4*c^2)).mp he
  have hnon : 0 ≤ 2*c*r*δ := by positivity
  have hnorm := norm_nonneg (z-(c : ℂ)^2)
  nlinarith [sq_nonneg (‖z-(c : ℂ)^2‖-2*c*r*δ)]

/-- Uniform quadratic comparison survives removal of both actual roots,
with the exact free normalization, on the full closed disc. -/
theorem norm_normalizedQuadraticDeflation_sub_one_le
    (c r δ : ℝ) (hc : 0 < c) (hr : 0 < r) (hδ : 0 ≤ δ) (hδ4 : δ ≤ 1/4)
    (f : ℂ → ℂ) (a b : ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall ((c : ℂ)^2) (c*r)))
    (ha : a ∈ closedBall ((c : ℂ)^2) (c*r))
    (hb : b ∈ closedBall ((c : ℂ)^2) (c*r))
    (hfa : f a = 0) (hfb : f b = 0) (hab : a = b → deriv f a = 0)
    (he : ∀ z ∈ closedBall ((c : ℂ)^2) (c*r),
      ‖f z- (-(z-(c : ℂ)^2)^2/(4*(c : ℂ)^2))‖ ≤ δ^2*r^2)
    (z : ℂ) (hz : z ∈ closedBall ((c : ℂ)^2) (c*r)) :
    ‖normalizedQuadraticDeflation c f a b z-1‖ ≤ 24*δ := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hda := norm_root_sub_center_le_of_quadratic_error c r δ hc hr hδ f a hfa (he a ha)
  have hdb := norm_root_sub_center_le_of_quadratic_error c r δ hc hr hδ f b hfb (he b hb)
  have hnear : 2*c*r*δ ≤ (c*r)/2 := by nlinarith [mul_pos hc hr]
  have hQ := analyticOnNhd_twoRootDeflation f _ a b hf ha hb
  let Q₀ : ℂ → ℂ := fun _ => -(1 : ℂ)/(4*(c : ℂ)^2)
  have hmodel (w : ℂ) :
      -(w-(c : ℂ)^2)^2/(4*(c : ℂ)^2) = (w-(c : ℂ)^2)^2*Q₀ w := by
    dsimp [Q₀]
    ring
  have hnormmodel (w : ℂ) : ‖Q₀ w‖ ≤ 1/(4*c^2) := by
    dsimp [Q₀]
    simp [abs_of_pos hc]
  have hbnd := norm_twoRootQuotient_sub_le_of_analyticOnNhd f
    (fun w => -(w-(c : ℂ)^2)^2/(4*(c : ℂ)^2))
    (twoRootDeflation f a b) Q₀ a b ((c : ℂ)^2) (c*r) (2*c*r*δ)
    (δ^2*r^2) (1/(4*c^2)) (mul_pos hc hr) (by positivity) hnear (by positivity)
    hda hdb hQ analyticOnNhd_const
    (fun w _ => twoRootDeflation_factor f a b hfa hfb hab w)
    (fun w _ => hmodel w) (fun w hw => he w (sphere_subset_closedBall hw))
    (fun w _ => hnormmodel w) z (by simpa only [mem_closedBall, dist_eq_norm] using hz)
  have hscale : normalizedQuadraticDeflation c f a b z-1 =
      (-4*(c : ℂ)^2)*(twoRootDeflation f a b z-Q₀ z) := by
    dsimp [normalizedQuadraticDeflation, Q₀]
    field_simp
    ring
  have hnormscale : ‖(-4 : ℂ)*(c : ℂ)^2‖ = 4*c^2 := by simp [abs_of_pos hc]
  rw [hscale, norm_mul, hnormscale]
  calc
    _ ≤ 4*c^2*(4*(δ^2*r^2+1/(4*c^2)*(2*(c*r)*(2*c*r*δ)+(2*c*r*δ)^2))/(c*r)^2) :=
      mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ = 16*δ+32*δ^2 := by field_simp; ring
    _ ≤ 24*δ := by nlinarith

end NLS.ComplexAnalysis
