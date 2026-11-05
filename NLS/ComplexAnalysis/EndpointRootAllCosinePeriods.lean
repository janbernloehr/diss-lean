import NLS.ComplexAnalysis.EndpointRootCosinePeriod

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem circleIntegral_div_endpointRoot_eq_cosine_integral_all
    (g : ℂ → ℂ) (τ δ : ℂ) (r R : ℝ) (hr : ‖δ‖ < r) (hrR : r < R)
    (hg : AnalyticOnNhd ℂ g (closedBall τ R)) :
    (∮ z in C(τ,r), g z/endpointRoot (τ-δ) (τ+δ) z) =
      -2*I*(∫ θ in (0 : ℝ)..Real.pi, g (cosineGapPoint τ δ (θ : ℂ))) := by
  by_cases hδ : δ = 0
  · subst δ
    have hrpos : 0 < r := by simpa only [norm_zero] using hr
    have hroot (z : ℂ) : endpointRoot (τ-0) (τ+0) z = τ-z := by
      simp only [sub_zero,add_zero,endpointRoot,sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        show (τ+τ)/2 = τ by ring,NLS.ZakharovShabat.normalizedStandardRoot_zeroGap]
    have hc : (∮ z in C(τ,r), g z/(z-τ)) = (2*Real.pi*I)*g τ := by
      simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
        (hg.mono (closedBall_subset_closedBall hrR.le)).differentiableOn.circleIntegral_sub_inv_smul
          (mem_ball_self hrpos)
    have he : (fun z => g z/endpointRoot (τ-0) (τ+0) z) = (fun z => (-1 : ℂ)*(g z/(z-τ))) := by
      funext z
      rw [hroot,show τ-z = -(z-τ) by ring,div_neg]
      ring
    rw [he,circleIntegral.integral_const_mul,hc]
    simp only [cosineGapPoint,zero_mul,add_zero,intervalIntegral.integral_const,sub_zero,Complex.real_smul]
    ring
  · exact circleIntegral_div_endpointRoot_eq_cosine_integral g τ δ r R hδ hr hrR hg

end NLS.ComplexAnalysis
