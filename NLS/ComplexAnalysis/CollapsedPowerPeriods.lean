import NLS.ComplexAnalysis.TwoZeroDeflation

/-! # Filled power periods at a collapsed branch point

A continuous square-root identity on a punctured neighborhood fixes the
value at its center. Analytic divided differences then fill the squared
critical denominator, including the power-two case.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem root_zero_of_punctured_square (B K : ℂ → ℂ) (U : Set ℂ) (a : ℂ)
    (hU : IsOpen U) (ha : a ∈ U) (hB : ContinuousAt B a) (hK : ContinuousAt K a)
    (hzero : K a = 0) (hsq : ∀ z ∈ U, z ≠ a → B z^2 = K z) : B a = 0 := by
  have he : (fun z => B z^2) =ᶠ[𝓝[≠] a] K := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds ha),self_mem_nhdsWithin]
      with z hz hza
    exact hsq z hz hza
  apply sq_eq_zero_iff.mp
  exact (tendsto_nhds_unique_of_eventuallyEq (hB.pow 2).continuousWithinAt
    hK.continuousWithinAt he).trans hzero

theorem circleIntegral_power_div_sq_eq_zero_of_analytic_zero
    (B : ℂ → ℂ) (a c : ℂ) (r : ℝ) (hr : 0 < r)
    (ha : a ∈ ball c r) (hB : AnalyticOnNhd ℂ B (closedBall c r))
    (hzero : B a = 0) (m : ℕ) :
    (∮ z in C(c,r), B z^(m+2)/(z-a)^2) = 0 := by
  let Q : ℂ → ℂ := dslope B a
  have hQ : AnalyticOnNhd ℂ Q (closedBall c r) :=
    analyticOnNhd_dslope_of_analytic B _ a hB (ball_subset_closedBall ha)
  have hf : AnalyticOnNhd ℂ (fun z => B z^m*Q z^2) (closedBall c r) :=
    (hB.pow m).mul (hQ.pow 2)
  have hfactor (z : ℂ) : B z = (z-a)*Q z := by
    have he := sub_smul_dslope B a z
    simpa only [smul_eq_mul,hzero,sub_zero] using he.symm
  have he : (∮ z in C(c,r), B z^(m+2)/(z-a)^2) =
      ∮ z in C(c,r), B z^m*Q z^2 := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hne : z-a ≠ 0 := by
      intro he
      have hz' : z ∈ ball c r := sub_eq_zero.mp he ▸ ha
      have hs := mem_sphere_iff_norm.mp hz
      have hb := mem_ball_iff_norm.mp hz'
      linarith
    change B z^(m+2)/(z-a)^2 = B z^m*Q z^2
    rw [pow_add,hfactor z]
    field_simp
  rw [he]
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
    hf.continuousOn (fun z hz => (hf z (ball_subset_closedBall hz.1)).differentiableAt)

end NLS.ComplexAnalysis
