import NLS.ComplexAnalysis.EndpointRootAllCosinePeriods
import NLS.ComplexAnalysis.QuadraticRootContourPeriod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exact quartic-gap factor of a cubic normalized-root period -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory
namespace NLS.ComplexAnalysis

/-- The cubic moment of an analytic root amplitude has a literal fourth
half-gap factor, with the original counterclockwise contour orientation.
The identity includes a collapsed gap and arbitrary complex endpoints. -/
theorem circleIntegral_cubic_endpointRoot_eq_fourth_gap
    (H : ℂ → ℂ) (τ δ : ℂ) (r R : ℝ) (hr : ‖δ‖ < r) (hrR : r < R)
    (hH : AnalyticOnNhd ℂ H (closedBall τ R)) :
    (∮ z in C(τ,r), (H z*endpointRoot (τ-δ) (τ+δ) z)^3) =
      -2*I*δ^4*(∫ θ in (0 : ℝ)..Real.pi,
        (Real.sin θ : ℂ)^4*H (cosineGapPoint τ δ (θ : ℂ))^3) := by
  let P : ℂ → ℂ := fun z => (z-τ)^2-δ^2
  let g : ℂ → ℂ := fun z => H z^3*(P z)^2
  have hg : AnalyticOnNhd ℂ g (closedBall τ R) :=
    (hH.pow 3).mul ((((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).sub
      analyticOnNhd_const).pow 2)
  have he (z : ℂ) (hz : z ∈ sphere τ r) :
      g z/endpointRoot (τ-δ) (τ+δ) z=(H z*endpointRoot (τ-δ) (τ+δ) z)^3 := by
    have hseg : segment ℝ (τ-δ) (τ+δ) ⊆ ball τ r :=
      (convex_ball τ r).segment_subset
        (by simpa only [mem_ball,dist_eq_norm,sub_sub_cancel_left,norm_neg] using hr)
        (by simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hr)
    have hzcut : z ∉ segment ℝ (τ-δ) (τ+δ) := fun h => sphere_disjoint_ball.le_bot ⟨hz,hseg h⟩
    have hs : endpointRoot (τ-δ) (τ+δ) z^2=P z :=
      (endpointRoot_sq _ _ z hzcut).trans (by dsimp [P];ring)
    dsimp only [g]
    rw [←hs]
    field_simp [endpointRoot_ne_zero _ _ z hzcut]
  have hcos (θ : ℝ) : g (cosineGapPoint τ δ (θ : ℂ)) =
      δ^4*((Real.sin θ : ℂ)^4*H (cosineGapPoint τ δ (θ : ℂ))^3) := by
    have hp : P (cosineGapPoint τ δ (θ : ℂ)) = -δ^2*(Real.sin θ : ℂ)^2 := by
      dsimp only [P,cosineGapPoint]
      rw [←ofReal_cos]
      have hs : (Real.sin θ : ℂ)^2+(Real.cos θ : ℂ)^2=1 := by
        rw [←ofReal_pow,←ofReal_pow,←ofReal_add,Real.sin_sq_add_cos_sq,ofReal_one]
      linear_combination δ^2*hs
    dsimp only [g]
    rw [hp]
    ring
  have hi := circleIntegral_div_endpointRoot_eq_cosine_integral_all g τ δ r R hr hrR hg
  rw [circleIntegral.integral_congr (norm_nonneg δ |>.trans hr.le) he] at hi
  simp_rw [hcos] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  exact hi.trans (by ring)

theorem integral_complex_sin_fourth :
    (∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^4) = 3*(Real.pi : ℂ)/8 := by
  have h2 : (∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ)^2)=Real.pi/2 := by
    simp [integral_sin_sq]
  have h4 : (∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ)^4)=3*Real.pi/8 := by
    rw [show (4 : ℕ)=2+2 by omega,integral_sin_pow]
    simp only [Real.sin_pi,Real.sin_zero,zero_pow (by norm_num : (3 : ℕ) ≠ 0),
      zero_mul,sub_zero,zero_div,h2]
    norm_num
    ring
  simp only [←ofReal_pow,intervalIntegral.integral_ofReal,h4,ofReal_div,ofReal_mul,ofReal_ofNat]

end NLS.ComplexAnalysis
