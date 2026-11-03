import NLS.ComplexAnalysis.EndpointRootCirclePeriod
import NLS.ComplexAnalysis.CosineZeroPeriod

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem circleIntegral_div_endpointRoot_eq_cosine_integral
    (g : ℂ → ℂ) (τ δ : ℂ) (r R : ℝ) (hδ : δ ≠ 0) (hr : ‖δ‖ < r) (hrR : r < R)
    (hg : AnalyticOnNhd ℂ g (closedBall τ R)) :
    (∮ z in C(τ,r), g z/endpointRoot (τ-δ) (τ+δ) z) =
      -2*I*(∫ θ in (0 : ℝ)..Real.pi, g (cosineGapPoint τ δ (θ : ℂ))) := by
  let Q := endpointRoot (τ-δ) (τ+δ)
  let J := ∮ z in C(τ,r), g z/Q z
  let K : ℂ := -(2*(Real.pi : ℂ)*I)
  let c := J/K
  have hrpos : 0 < r := (norm_nonneg δ).trans_lt hr
  have hgap : segment ℝ (τ-δ) (τ+δ) ⊆ ball τ r := by
    apply (convex_ball _ _).segment_subset
    · simpa only [mem_ball,dist_eq_norm,sub_sub_cancel_left,norm_neg] using hr
    · simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hr
  have hQ : AnalyticOnNhd ℂ Q (closedBall τ R \ segment ℝ (τ-δ) (τ+δ)) :=
    (analyticOnNhd_endpointRoot (τ-δ) (τ+δ)).mono (fun _ hz => hz.2)
  have hsquare (z : ℂ) (hz : z ∈ closedBall τ R \ segment ℝ (τ-δ) (τ+δ)) :
      Q z^2 = (τ-δ-z)*(τ+δ-z) := by
    rw [endpointRoot_sq _ _ z hz.2]
    ring
  have hKne : K ≠ 0 := by dsimp only [K];simp [Real.pi_ne_zero]
  have hpone : (∮ z in C(τ,r), 1/Q z) = K := by
    simpa only [one_div] using circleIntegral_inv_endpointRoot_midpoint τ δ r hr
  have hcircle (z : ℂ) (hz : z ∈ sphere τ r) : z ∉ segment ℝ (τ-δ) (τ+δ) :=
    fun he => sphere_disjoint_ball.le_bot ⟨hz,hgap he⟩
  have hQne (z : ℂ) (hz : z ∈ sphere τ r) : Q z ≠ 0 := by
    intro he
    have hs := endpointRoot_sq (τ-δ) (τ+δ) z (hcircle z hz)
    have hz1 : z-(τ-δ) ≠ 0 := sub_ne_zero.mpr (fun hh => hcircle z hz (hh ▸ left_mem_segment ℝ _ _))
    have hz2 : z-(τ+δ) ≠ 0 := sub_ne_zero.mpr (fun hh => hcircle z hz (hh ▸ right_mem_segment ℝ _ _))
    change Q z^2 = _ at hs
    rw [he,zero_pow (by norm_num : 2 ≠ 0)] at hs
    exact mul_ne_zero hz1 hz2 hs.symm
  have hgci : CircleIntegrable (fun z => g z/Q z) τ r :=
    ((hg.mono (sphere_subset_closedBall.trans (closedBall_subset_closedBall hrR.le))).continuousOn.div
      ((analyticOnNhd_endpointRoot _ _).continuousOn.mono hcircle) hQne).circleIntegrable hrpos.le
  have hqci : CircleIntegrable (fun z => 1/Q z) τ r :=
    (continuousOn_const.div ((analyticOnNhd_endpointRoot _ _).continuousOn.mono hcircle) hQne).circleIntegrable hrpos.le
  have hperiod : (∮ z in C(τ,r), (g z-c)/Q z) = 0 := by
    have he : (fun z => (g z-c)/Q z) = (fun z => g z/Q z-c*(1/Q z)) := by funext z;ring
    have hcint : CircleIntegrable (fun z => c*(1/Q z)) τ r := by
      simpa only [smul_eq_mul] using hqci.const_fun_smul (a := c)
    rw [he,circleIntegral.integral_sub hgci hcint,circleIntegral.integral_const_mul,hpone]
    change J-c*K = 0
    dsimp only [c]
    rw [div_mul_cancel₀ _ hKne,sub_self]
  have hzero := integral_cosineGapPoint_eq_zero_of_zero_period (fun z => g z-c) Q τ δ τ r R hδ hrpos hrR hgap
    (hg.sub analyticOnNhd_const) hQ hsquare hperiod
  have hcont : ContinuousOn (fun θ : ℝ => g (cosineGapPoint τ δ (θ : ℂ))) (Icc 0 Real.pi) :=
    hg.continuousOn.comp (by unfold cosineGapPoint;fun_prop)
      (fun θ _ => ball_subset_closedBall (ball_subset_ball hrR.le (hgap (cosineGapPoint_real_mem_segment τ δ θ))))
  have hint : IntervalIntegrable (fun θ : ℝ => g (cosineGapPoint τ δ (θ : ℂ))) volume 0 Real.pi :=
    hcont.intervalIntegrable_of_Icc Real.pi_pos.le
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const,intervalIntegral.integral_const,
    sub_zero,Complex.real_smul] at hzero
  change (∫ θ in (0 : ℝ)..Real.pi, g (cosineGapPoint τ δ (θ : ℂ)))- (Real.pi : ℂ)*c = 0 at hzero
  have hm := sub_eq_zero.mp hzero
  rw [hm]
  dsimp only [c,K]
  field_simp
  ring

end NLS.ComplexAnalysis
