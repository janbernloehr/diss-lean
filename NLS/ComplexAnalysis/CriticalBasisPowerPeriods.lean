import NLS.ComplexAnalysis.CriticalBasisPeriodBounds

/-! # All power moments of a filled critical numerator

Integration by parts uses only the actual numerator factor identity and
nonvanishing of its selected critical denominator on the contour.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem critical_basis_power_period_eq_primitive
    (F B R d : ℂ → ℂ) (mu b c : ℂ) (r : ℝ) (hr : 0 ≤ r) (m : ℕ)
    (hF : AnalyticOnNhd ℂ F (sphere c r))
    (hfactor : ∀ lambda, (lambda-mu)*B lambda = (2*b*Real.pi)*d lambda)
    (hderiv : ∀ z ∈ sphere c r, deriv F z = (d (z^2)/R (z^2))*(2*z))
    (hne : ∀ z ∈ sphere c r, z^2-mu ≠ 0) :
    (∮ z in C(c,r), F z^m*(B (z^2)/R (z^2))*(2*z)) =
      (2*b*Real.pi)/(m+1)*
        ∮ z in C(c,r), F z^(m+1)*(2*z)/(z^2-mu)^2 := by
  let G : ℂ → ℂ := fun z => z^2-mu
  have hG : AnalyticOnNhd ℂ G (sphere c r) := (analyticOnNhd_id.pow 2).sub analyticOnNhd_const
  have hDF (z : ℂ) (hz : z ∈ sphere c r) :
      deriv (fun w => F w^(m+1)) z = (m+1 : ℂ)*(F z^m*deriv F z) := by
    simpa only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,mul_assoc] using!
      ((hF z hz).differentiableAt.hasDerivAt.pow (m+1)).deriv
  have hDG (z : ℂ) : deriv G z = 2*z := by
    exact ((hasDerivAt_id z).pow 2 |>.sub_const _).deriv.trans (by simp)
  have hp := circleIntegral_deriv_div_eq (fun z => F z^(m+1)) G c r hr (hF.pow (m+1)) hG hne
  have he (z : ℂ) (hz : z ∈ sphere c r) :
      F z^m*(B (z^2)/R (z^2))*(2*z) =
        ((2*b*Real.pi)/(m+1))*(deriv (fun w => F w^(m+1)) z/G z) := by
    have hb : B (z^2) = (2*b*Real.pi)*d (z^2)/G z := by
      apply (eq_div_iff (hne z hz)).mpr
      exact (mul_comm _ _).trans (hfactor (z^2))
    rw [hb,hDF z hz,hderiv z hz]
    have hm : (m+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    field_simp [hm]
  rw [circleIntegral.integral_congr hr he,circleIntegral.integral_const_mul,hp]
  simp_rw [hDG]
  rfl

end NLS.ComplexAnalysis
