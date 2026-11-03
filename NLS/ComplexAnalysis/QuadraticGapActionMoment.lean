import NLS.ComplexAnalysis.SineSquareCosineMoments
import NLS.ComplexAnalysis.EndpointRootAllCosinePeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem circleIntegral_mul_div_endpointRoot_eq_squared_gap
    (g : ℂ → ℂ) (τ δ : ℂ) (r R : ℝ) (hr : ‖δ‖ < r) (hrR : r < R)
    (hg : AnalyticOnNhd ℂ g (closedBall τ R))
    (hperiod : (∮ z in C(τ,r), g z/endpointRoot (τ-δ) (τ+δ) z) = 0) :
    (∮ z in C(τ,r), z*g z/endpointRoot (τ-δ) (τ+δ) z) =
      -2*I*δ^2*(∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*deriv g (τ+δ*(Real.cos θ : ℂ))) := by
  have hsegment (θ : ℝ) : τ+δ*(Real.cos θ : ℂ) ∈ closedBall τ R := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_mul]
    have hc : ‖(Real.cos θ : ℂ)‖ ≤ 1 := by simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
    exact (mul_le_mul_of_nonneg_left hc (norm_nonneg δ)).trans (by simpa only [mul_one] using hr.le.trans hrR.le)
  have hmean := circleIntegral_div_endpointRoot_eq_cosine_integral_all g τ δ r R hr hrR hg
  rw [hperiod] at hmean
  have hzero : (∫ θ in (0 : ℝ)..Real.pi, g (τ+δ*(Real.cos θ : ℂ))) = 0 := by
    have h := (mul_eq_zero.mp hmean.symm).resolve_left (by simp : (-2*I : ℂ) ≠ 0)
    simpa only [cosineGapPoint,← ofReal_cos] using h
  have hcont : Continuous (fun θ : ℝ => τ+δ*(Real.cos θ : ℂ)) := by fun_prop
  have hG : ContinuousOn (fun θ : ℝ => g (τ+δ*(Real.cos θ : ℂ))) (Icc (0 : ℝ) Real.pi) :=
    hg.continuousOn.comp hcont.continuousOn (fun θ _ => hsegment θ)
  have hcos : Continuous (fun θ : ℝ => (Real.cos θ : ℂ)) := continuous_ofReal.comp Real.continuous_cos
  have hGi : IntervalIntegrable (fun θ : ℝ => g (τ+δ*(Real.cos θ : ℂ))) volume 0 Real.pi :=
    hG.intervalIntegrable_of_Icc Real.pi_pos.le
  have hCi : IntervalIntegrable (fun θ : ℝ => (Real.cos θ : ℂ)*g (τ+δ*(Real.cos θ : ℂ))) volume 0 Real.pi :=
    (hcos.continuousOn.mul hG).intervalIntegrable_of_Icc Real.pi_pos.le
  have he : (fun θ : ℝ => (τ+δ*(Real.cos θ : ℂ))*g (τ+δ*(Real.cos θ : ℂ))) =
      (fun θ : ℝ => τ*g (τ+δ*(Real.cos θ : ℂ))+δ*((Real.cos θ : ℂ)*g (τ+δ*(Real.cos θ : ℂ)))) := by
    funext θ
    ring
  have hi := circleIntegral_div_endpointRoot_eq_cosine_integral_all (fun z => z*g z) τ δ r R hr hrR (analyticOnNhd_id.mul hg)
  simp only [cosineGapPoint,← ofReal_cos] at hi
  rw [he,intervalIntegral.integral_add (hGi.const_mul τ) (hCi.const_mul δ),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hzero,mul_zero,zero_add,
    cosine_first_moment_eq_sine_square_deriv g τ δ (closedBall τ R) hg (fun θ _ => hsegment θ)] at hi
  exact hi.trans (by ring)

end NLS.ComplexAnalysis
