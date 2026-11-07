import NLS.ComplexAnalysis.BanachHolomorphicC1
import NLS.ComplexAnalysis.NearIdentityAnalyticInverse

/-! A common outer ball and norm bound give common analytic inverse
radii for EVERY holomorphic map normalized to value zero and derivative
identity at the origin. All radii are chosen before the map. -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem exists_uniform_normalized_analytic_inverse_radii (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧ ρ < R ∧
      ∀ f : E → E, AnalyticOnNhd ℂ f (ball 0 (4*R)) →
        (∀ x ∈ ball (0:E) (4*R), ‖f x‖ ≤ M) → f 0 = 0 →
        fderiv ℂ f 0 = ContinuousLinearMap.id ℂ E →
        ∃ g : E → E, AnalyticOnNhd ℂ g (ball 0 δ) ∧ g 0 = 0 ∧
          ∀ y ∈ ball (0:E) δ, g y ∈ ball 0 ρ ∧ f (g y) = y ∧
            ∀ x ∈ ball (0:E) ρ, f x = y → x = g y := by
  let L : ℝ := 4*M/R^2
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  let r : ℝ := min R (1/(4*(L+1)))
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrR : r ≤ R := min_le_left _ _
  have hsmall : L*r ≤ (1/2:ℝ) := by
    have hb := (le_div_iff₀ (by positivity : 0 < 4*(L+1))).mp (min_le_right R (1/(4*(L+1))))
    change r*(4*(L+1)) ≤ 1 at hb
    nlinarith
  let ρ := quantitativeInverseJointRadius r 2 L
  let δ := quantitativeInverseImageRadius r 2 L
  have hρ : 0 < ρ := quantitativeInverseJointRadius_pos hr (by norm_num) hL
  have hδ : 0 < δ := quantitativeInverseImageRadius_pos hr (by norm_num) hL
  have hρR : ρ < R := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨ρ,δ,hρ,hδ,hρR,?_⟩
  intro f hf hb hzero hder
  have hLip {x y : E} (hx : x ∈ ball (0:E) R) (hy : y ∈ ball (0:E) R) :
      ‖fderiv ℂ f y-fderiv ℂ f x‖ ≤ L*‖y-x‖ :=
    norm_fderiv_sub_le_of_holomorphic_ball_bound f 0 R M hR hf.differentiableOn hb hx hy
  have hnear (x : E) (hx : x ∈ ball (0:E) r) :
      ‖fderiv ℂ f x-ContinuousLinearMap.id ℂ E‖ ≤ (1/2:ℝ) := by
    rw [← hder]
    have hn : ‖x‖ < r := mem_ball_zero_iff.mp hx
    have hfirst : ‖fderiv ℂ f x-fderiv ℂ f 0‖ ≤ L*‖x‖ := by
      simpa only [sub_zero] using hLip (mem_ball_self hR) ((ball_subset_ball hrR) hx)
    exact hfirst.trans ((mul_le_mul_of_nonneg_left hn.le hL).trans hsmall)
  obtain ⟨g,hg,hgzero,hginv⟩ := exists_analytic_inverse_of_derivative_near_id f 0 r L hr hL
    (hf.mono (ball_subset_ball (by linarith : r ≤ 4*R))) hnear
    (fun x hx y hy => by simpa only [norm_sub_rev] using hLip ((ball_subset_ball hrR) hy) ((ball_subset_ball hrR) hx))
  rw [hzero] at hg hgzero hginv
  exact ⟨g,hg,hgzero,hginv⟩

end NLS.ComplexAnalysis
