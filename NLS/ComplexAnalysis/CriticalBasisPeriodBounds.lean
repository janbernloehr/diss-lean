import NLS.ComplexAnalysis.RationalCircleIntegrationByParts
import NLS.KdV.HighEnergyContourSeparation

/-! # Critical-basis periods as squared-resolvent primitive integrals -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem critical_basis_period_eq_primitive
    (H B R d : ℂ → ℂ) (mu b c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hH : AnalyticOnNhd ℂ H (sphere c r))
    (hfactor : ∀ lambda, (lambda-mu)*B lambda = (2*b*Real.pi)*d lambda)
    (hderiv : ∀ z ∈ sphere c r, deriv H z = (d (z^2)/R (z^2))*(2*z))
    (hne : ∀ z ∈ sphere c r, z^2-mu ≠ 0) :
    (2*(Real.pi : ℂ))⁻¹ * (∮ z in C(c,r), (B (z^2)/R (z^2))*(2*z)) =
      b * ∮ z in C(c,r), H z*(2*z)/(z^2-mu)^2 := by
  let G : ℂ → ℂ := fun z => z^2-mu
  have hG : AnalyticOnNhd ℂ G (sphere c r) := (analyticOnNhd_id.pow 2).sub analyticOnNhd_const
  have hDG (z : ℂ) : deriv G z = 2*z := by
    exact ((hasDerivAt_id z).pow 2 |>.sub_const _).deriv.trans (by simp)
  have hp := circleIntegral_deriv_div_eq H G c r hr hH hG hne
  have hpoint (z : ℂ) (hz : z ∈ sphere c r) :
      (B (z^2)/R (z^2))*(2*z) = (2*b*Real.pi)*(deriv H z/G z) := by
    have hb : B (z^2) = (2*b*Real.pi)*d (z^2)/G z := by
      apply (eq_div_iff (hne z hz)).mpr
      exact (mul_comm _ _).trans (hfactor (z^2))
    rw [hb,hderiv z hz]
    simp only [div_eq_mul_inv]
    ring
  rw [circleIntegral.integral_congr hr hpoint,circleIntegral.integral_const_mul,hp]
  simp_rw [hDG]
  change (2*(Real.pi : ℂ))⁻¹*((2*b*Real.pi)*(∮ z in C(c,r), H z*(2*z)/(G z)^2)) = _
  rw [← mul_assoc]
  congr 1
  field_simp

theorem norm_frequency_primitive_resolvent_integral_le (H : ℂ → ℂ) (mu : ℂ)
    (k : ℕ+) (A d : ℝ) (hA : 0 ≤ A) (hd : 0 < d)
    (hH : ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4), ‖H z‖ ≤ A)
    (hden : ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4), d ≤ ‖z^2-mu‖) :
    ‖∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), H z*(2*z)/(z^2-mu)^2‖ ≤
      2*Real.pi*(Real.pi/4)*(A*((5*Real.pi/2)*(k : ℝ))/d^2) := by
  apply circleIntegral.norm_integral_le_of_norm_le_const (by positivity)
  intro z hz
  have hzc : ‖z-(Real.pi : ℂ)*(k : ℕ)‖ = Real.pi/4 := mem_sphere_iff_norm.mp hz
  have hcn : ‖(Real.pi : ℂ)*(k : ℕ)‖ = Real.pi*(k : ℝ) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_natCast]
  have ht := norm_add_le (z-(Real.pi : ℂ)*(k : ℕ)) ((Real.pi : ℂ)*(k : ℕ))
  rw [sub_add_cancel,hzc,hcn] at ht
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hzbound : ‖(2 : ℂ)*z‖ ≤ (5*Real.pi/2)*(k : ℝ) := by
    rw [norm_mul]
    norm_num only [norm_ofNat]
    nlinarith [Real.pi_pos]
  rw [norm_div,norm_mul,norm_pow]
  gcongr
  · exact hH z hz
  · exact hden z hz

end NLS.ComplexAnalysis
