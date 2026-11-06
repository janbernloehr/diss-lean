import NLS.ComplexAnalysis.JointSpectralDerivativeAnalytic
import NLS.ComplexAnalysis.QuadraticGapActionRatio
import NLS.ComplexAnalysis.AnalyticDiscDerivativeBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.ComplexAnalysis



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem analyticAt_quadraticGapActionRatio_of_disc
    (H : ℂ × A → ℂ) (t s : A → ℂ) (a : A)
    (ht : AnalyticAt ℂ t a) (hs : AnalyticAt ℂ s a)
    (R : ℝ) (hR : ‖sqrt (s a)‖ < R)
    (hH : ∀ z ∈ closedBall (t a) R, AnalyticAt ℂ H (z,a)) :
    AnalyticAt ℂ (quadraticGapActionRatio H t s) a := by
  let D : Set (ℂ × A) := {x | AnalyticAt ℂ H x}
  have hD : IsOpen D := isOpen_analyticAt ℂ H
  have hd : AnalyticOnNhd ℂ (fun x : ℂ × A => deriv (fun w => H (w,x.2)) x.1) D :=
    analyticOnNhd_spectral_deriv_of_analyticOnNhd H D hD (fun _ hx => hx)
  have hsq : AnalyticAt ℂ (fun p : A => (sqrt (s p))^2) a := by
    simpa only [complex_sqrt_sq] using hs
  exact analyticAt_const.mul (analyticAt_parametricSineSquareCosineMean_of_analytic_square
    _ t (fun p => sqrt (s p)) D hD hd a ht hsq R hR hH)

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
    exact (norm_deriv_le_of_analytic_closedDisc_bound _ hH (by linarith : R/2<R) C hb hz).trans_eq (by field_simp;ring)
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
