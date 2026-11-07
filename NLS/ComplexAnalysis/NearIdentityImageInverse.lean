import NLS.ComplexAnalysis.NearIdentityBallInverse
import NLS.ComplexAnalysis.AnalyticInjectiveImage

/-! A near-identity analytic inverse on an open image surrounding the
ENTIRE image of the closed inner source ball,including its boundary. -/
noncomputable section
open Set Metric
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A smaller Cauchy radius controls the derivative on an intermediate ball. -/
theorem norm_fderiv_sub_id_le_on_intermediate_ball (f : E → E) (m : ℝ) (hm : 0 < m)
    (hf : AnalyticOnNhd ℂ f (ball 0 (2*m)))
    (hb : ∀ x ∈ ball (0:E) (2*m), ‖f x-x‖ ≤ m/32)
    (x : E) (hx : ‖x‖ ≤ 3*m/2) :
    ‖fderiv ℂ f x-ContinuousLinearMap.id ℂ E‖ ≤ (1/8 : ℝ) := by
  let g : E → E := fun z => f z-z
  have hsub : ball x (m/2) ⊆ ball (0:E) (2*m) := by
    intro z hz
    have hzn : ‖z-x‖ < m/2 := by simpa only [mem_ball, dist_eq_norm] using hz
    have hn := norm_le_norm_sub_add z x
    rw [mem_ball_zero_iff]
    linarith
  have hx2 : x ∈ ball (0:E) (2*m) := by rw [mem_ball_zero_iff]; linarith
  have hg : DifferentiableOn ℂ g (ball x (m/2)) := by
    intro z hz
    exact ((hf z (hsub hz)).differentiableAt.sub differentiableAt_id).differentiableWithinAt
  have hmaps : MapsTo g (ball x (m/2)) (closedBall (g x) (m/16)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le (g z) (g x)).trans (by
      have hz' := hb z (hsub hz)
      have hx' := hb x hx2
      dsimp [g]
      linarith)
  have hder := Complex.norm_fderiv_le_div_of_mapsTo_ball hg hmaps (by positivity : 0 < m/2)
  have he : fderiv ℂ g x = fderiv ℂ f x-ContinuousLinearMap.id ℂ E :=
    ((hf x hx2).differentiableAt.hasFDerivAt.sub (hasFDerivAt_id x)).fderiv
  rw [he] at hder
  exact hder.trans_eq (by field_simp [hm.ne']; norm_num)

/-- The actual open image of the intermediate source ball carries one analytic
inverse. In particular it surrounds every image point of the closed inner ball. -/
theorem exists_analytic_inverse_on_near_identity_image (f : E → E) (m : ℝ) (hm : 0 < m)
    (hf : AnalyticOnNhd ℂ f (ball 0 (2*m)))
    (hb : ∀ x ∈ ball (0:E) (2*m), ‖f x-x‖ ≤ m/32) :
    ∃ g : E → E,
      IsOpen (f '' ball 0 (3*m/2)) ∧ AnalyticOnNhd ℂ g (f '' ball 0 (3*m/2)) ∧
      Set.InjOn f (ball 0 (3*m/2)) ∧
      (∀ x ∈ ball (0:E) (3*m/2), g (f x) = x) ∧
      ∀ y ∈ f '' ball (0:E) (3*m/2), g y ∈ ball 0 (3*m/2) ∧ f (g y) = y := by
  have hsub : ball (0:E) (3*m/2) ⊆ ball 0 (2*m) := ball_subset_ball (by linarith)
  have hfU := hf.mono hsub
  have hnear (x : E) (hx : x ∈ ball (0:E) (3*m/2)) :
      ‖fderiv ℂ f x-ContinuousLinearMap.id ℂ E‖ ≤ (1/2 : ℝ) :=
    (norm_fderiv_sub_id_le_on_intermediate_ball f m hm hf hb x (mem_ball_zero_iff.mp hx).le).trans (by norm_num)
  have hi : Set.InjOn f (ball (0:E) (3*m/2)) := by
    intro x hx y hy hxy
    have hh := norm_sub_le_two_mul_norm_image_sub_of_derivative_near_id
      f 0 (3*m/2) hfU hnear x y hx hy
    rw [hxy, sub_self, norm_zero, mul_zero] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  have hd (x : E) (hx : x ∈ ball (0:E) (3*m/2)) : Function.Bijective (fderiv ℂ f x) := by
    obtain ⟨e, he, _⟩ := exists_continuousLinearEquiv_of_norm_sub_id_le_half (fderiv ℂ f x) (hnear x hx)
    rw [← he]
    exact e.bijective
  obtain ⟨g, hopen, hA, hleft, hright⟩ := exists_analytic_inverse_on_injective_open_image f
    (ball 0 (3*m/2)) isOpen_ball hfU hi hd
  exact ⟨g, hopen, hA, hi, hleft, hright⟩

end NLS.ComplexAnalysis
