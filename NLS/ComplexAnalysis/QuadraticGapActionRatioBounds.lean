import NLS.ComplexAnalysis.QuadraticGapActionRatio
import NLS.ComplexAnalysis.DiscBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.ComplexAnalysis



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem norm_deriv_le_of_analytic_closedDisc_bound
    (f : ℂ → ℂ) (c : ℂ) (r R C : ℝ) (hrR : r<R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ z∈closedBall c R, ‖f z‖≤C) (z : ℂ) (hz : z∈closedBall c r) :
    ‖deriv f z‖≤C/(R-r) := by
  have hsub : closedBall z (R-r)⊆closedBall c R := by
    intro w hw
    have hw' : ‖w-z‖≤R-r := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have hz' : ‖z-c‖≤r := by simpa only [mem_closedBall,dist_eq_norm] using hz
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by linarith)
  have ha := hf.mono hsub
  have hdc : DiffContOnCl ℂ f (ball z (R-r)) :=
    DiffContOnCl.mk_ball (ha.differentiableOn.mono ball_subset_closedBall) ha.continuousOn
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (sub_pos.mpr hrR) hdc
    (fun w hw => hb w (hsub (sphere_subset_closedBall hw)))

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem norm_quadraticGapActionRatio_le_of_disc_bound
    (H : ℂ × A → ℂ) (t s : A → ℂ) (a : A) (R C : ℝ)
    (hR : 0<R) (_hC : 0≤C) (hd : ‖sqrt (s a)‖≤R/2)
    (hH : AnalyticOnNhd ℂ (fun z => H (z,a)) (closedBall (t a) R))
    (hb : ∀ z∈closedBall (t a) R, ‖H (z,a)‖≤C) :
    ‖quadraticGapActionRatio H t s a‖≤4*C/R := by
  have hg (θ : ℝ) : ‖deriv (fun z => H (z,a)) (t a+sqrt (s a)*(Real.cos θ:ℂ))‖≤2*C/R := by
    have hcos : ‖(Real.cos θ:ℂ)‖≤1 := by
      simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
    have hz : t a+sqrt (s a)*(Real.cos θ:ℂ)∈closedBall (t a) (R/2) := by
      rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_mul]
      exact (mul_le_mul_of_nonneg_left hcos (norm_nonneg _)).trans (by simpa only [mul_one] using hd)
    exact (norm_deriv_le_of_analytic_closedDisc_bound _ _ (R/2) R C (by linarith) hH hb _ hz).trans_eq (by field_simp;ring)
  have hi : ‖∫ θ in (0:ℝ)..Real.pi, (Real.sin θ:ℂ)^2*
      deriv (fun z => H (z,a)) (t a+sqrt (s a)*(Real.cos θ:ℂ))‖≤(2*C/R)*Real.pi := by
    have hb' (θ : ℝ) (_hθ : θ∈uIoc (0:ℝ) Real.pi) :
        ‖(Real.sin θ:ℂ)^2*deriv (fun z => H (z,a)) (t a+sqrt (s a)*(Real.cos θ:ℂ))‖≤2*C/R := by
      rw [norm_mul,norm_pow]
      have hs : ‖(Real.sin θ:ℂ)‖^2≤1 := by
        have hh : ‖(Real.sin θ:ℂ)‖≤1 := by simpa only [norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ
        nlinarith [norm_nonneg (Real.sin θ:ℂ)]
      exact (mul_le_mul hs (hg θ) (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)
    simpa only [sub_zero,abs_of_pos Real.pi_pos] using intervalIntegral.norm_integral_le_of_norm_le_const hb'
  unfold quadraticGapActionRatio parametricSineSquareCosineMean
  rw [norm_mul]
  have hc : ‖-2*I/(Real.pi:ℂ)‖=2/Real.pi := by
    norm_num only [norm_div,norm_mul,norm_neg,norm_ofNat,norm_I,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,mul_one]
  rw [hc]
  exact (mul_le_mul_of_nonneg_left hi (by positivity : 0≤2/Real.pi)).trans_eq (by field_simp;ring)

end NLS.ComplexAnalysis
