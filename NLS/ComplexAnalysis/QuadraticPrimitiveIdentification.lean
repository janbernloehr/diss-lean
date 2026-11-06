import NLS.ComplexAnalysis.NormalizedSegmentPrimitiveUnique
import NLS.ComplexAnalysis.QuadraticGapActionMoment
import NLS.ComplexAnalysis.QuadraticRootPrimitive
import NLS.ComplexAnalysis.QuadraticRootContourPeriod

/-! # Identifying a regular root amplitude with an actual normalized primitive -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem cosine_mean_eq_zero_of_primitive (g F : ℂ → ℂ) (τ δ : ℂ) (r R : ℝ)
    (hr : ‖δ‖ < r) (hrR : r < R)
    (hg : AnalyticOnNhd ℂ g (closedBall τ R))
    (hF : ∀ z ∈ sphere τ r, HasDerivAt F (g z/endpointRoot (τ-δ) (τ+δ) z) z) :
    (∫ θ in (0 : ℝ)..Real.pi, g (cosineGapPoint τ δ (θ : ℂ)))=0 := by
  have hz : (∮ z in C(τ,r), g z/endpointRoot (τ-δ) (τ+δ) z)=0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt ((norm_nonneg δ).trans hr.le)
      (fun z hz => (hF z hz).hasDerivWithinAt)
  have hi := circleIntegral_div_endpointRoot_eq_cosine_integral_all g τ δ r R hr hrR hg
  rw [hz] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left (by simp : (-2*I : ℂ) ≠ 0)

/-- The normalized endpoint value fixes the primitive and its sheet sign.
An open, closed or complex gap is permitted. -/
theorem root_amplitude_eq_normalized_primitive
    (H g F : ℂ → ℂ) (τ δ : ℂ) (R : ℝ) (hδ : ‖δ‖ < R)
    (hH : AnalyticOnNhd ℂ H (ball τ R))
    (he : ∀ z ∈ ball τ R,
      ((z-τ)^2-δ^2)*deriv H z+(z-τ)*H z=g z)
    (hF : ∀ z ∈ ball τ R \ segment ℝ (τ-δ) (τ+δ),
      HasDerivAt F (g z/endpointRoot (τ-δ) (τ+δ) z) z)
    (hzero : Tendsto F (𝓝[ball τ R \ segment ℝ (τ-δ) (τ+δ)] (τ-δ)) (𝓝 0)) :
    EqOn F (fun z => H z*endpointRoot (τ-δ) (τ+δ) z)
      (ball τ R \ segment ℝ (τ-δ) (τ+δ)) := by
  let K := segment ℝ (τ-δ) (τ+δ)
  have hl : τ-δ ∈ ball τ R := by
    simpa only [mem_ball,dist_eq_norm,sub_sub_cancel_left,norm_neg] using hδ
  have hclosed : IsClosed K := by
    apply IsCompact.isClosed
    change IsCompact (segment ℝ (τ-δ) (τ+δ))
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hG (z : ℂ) (hz : z ∈ ball τ R \ K) :
      HasDerivAt (fun w => endpointRoot (τ-δ) (τ+δ) w*H w)
        (g z/endpointRoot (τ-δ) (τ+δ) z) z := by
    apply hasDerivAt_root_mul_of_quadratic_equation _ H τ (δ^2) (g z) z
      (analyticOnNhd_endpointRoot _ _ z hz.2) (endpointRoot_ne_zero _ _ z hz.2) ?_ (hH z hz.1)
    · exact he z hz.1
    · filter_upwards [hclosed.isOpen_compl.mem_nhds hz.2] with w hw
      exact (endpointRoot_sq _ _ w hw).trans (by dsimp only [quadraticRootPolynomial];ring)
  have hroot : Tendsto (endpointRoot (τ-δ) (τ+δ))
      (𝓝[ball τ R \ K] (τ-δ)) (𝓝 0) := by
    apply tendsto_zero_of_sq_tendsto_zero
    have ht : Tendsto (fun z : ℂ => ((τ-δ)-z)*((τ+δ)-z))
        (𝓝[ball τ R \ K] (τ-δ)) (𝓝 0) := by
      simpa using!
        (((continuous_const (y := τ-δ)).sub continuous_id).mul
          ((continuous_const (y := τ+δ)).sub continuous_id)).continuousAt.tendsto.mono_left
          (nhdsWithin_le_nhds : 𝓝[ball τ R \ K] (τ-δ) ≤ 𝓝 (τ-δ))
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (show (τ-δ-z)*(τ+δ-z)=(z-(τ-δ))*(z-(τ+δ)) by ring).trans
      (endpointRoot_sq _ _ z hz.2).symm
  have hlim : Tendsto (fun z => endpointRoot (τ-δ) (τ+δ) z*H z)
      (𝓝[ball τ R \ K] (τ-δ)) (𝓝 0) := by
    simpa only [zero_mul] using hroot.mul ((hH _ hl).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hnorm := normalized_segment_primitives_eq_on_convex_complement
    (fun z => g z/endpointRoot (τ-δ) (τ+δ) z) F
    (fun z => endpointRoot (τ-δ) (τ+δ) z*H z) (ball τ R)
    (τ-δ) (τ+δ) 0 0 isOpen_ball (convex_ball τ R) hl hF hG hzero hlim
  intro z hz
  simpa only [sub_zero,mul_comm] using hnorm hz

end NLS.ComplexAnalysis
