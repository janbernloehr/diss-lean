import NLS.ComplexAnalysis.QuadraticCauchyEquation

/-!
# Multiplying a quadratic-equation solution by a root sheet

An analytic solution of the quadratic root equation becomes a primitive
on every regular analytic square-root sheet. The boundary value is zero
at a root of the quadratic, independently of the sign of the sheet.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem hasDerivAt_root_of_sq_eq_quadratic
    (Q : ℂ → ℂ) (τ d z : ℂ) (hQ : AnalyticAt ℂ Q z) (hne : Q z ≠ 0)
    (hsq : (fun v => Q v^2) =ᶠ[𝓝 z] quadraticRootPolynomial τ d) :
    HasDerivAt Q ((z-τ)/Q z) z := by
  have hqd : HasDerivAt Q (deriv Q z) z := hQ.differentiableAt.hasDerivAt
  have hsqDerivative := (hqd.pow 2).congr_of_eventuallyEq hsq.symm
  have hd := hsqDerivative.unique (hasDerivAt_quadraticRootPolynomial τ d z)
  have hv : deriv Q z = (z-τ)/Q z := by
    apply (eq_div_iff hne).2
    simp only [Nat.cast_ofNat,show (2:ℕ)-1 = 1 from rfl,pow_one] at hd
    linear_combination (1/2:ℂ)*hd
  rw [← hv]
  exact hqd

theorem hasDerivAt_root_mul_of_quadratic_equation
    (Q H : ℂ → ℂ) (τ d g z : ℂ)
    (hQ : AnalyticAt ℂ Q z) (hne : Q z ≠ 0)
    (hsq : (fun v => Q v^2) =ᶠ[𝓝 z] quadraticRootPolynomial τ d)
    (hH : AnalyticAt ℂ H z)
    (heq : quadraticRootPolynomial τ d z*deriv H z+(z-τ)*H z = g) :
    HasDerivAt (fun v => Q v*H v) (g/Q z) z := by
  have hs := hsq.eq_of_nhds
  have hv : ((z-τ)/Q z)*H z+Q z*deriv H z = g/Q z := by
    apply (eq_div_iff hne).2
    calc
      _ = Q z^2*deriv H z+(z-τ)*H z := by field_simp [hne]; ring
      _ = g := by rw [hs]; exact heq
  have hhd : HasDerivAt H (deriv H z) z := hH.differentiableAt.hasDerivAt
  rw [← hv]
  exact (hasDerivAt_root_of_sq_eq_quadratic Q τ d z hQ hne hsq).fun_mul hhd

/-- Squaring removes the branch sign: any complex root whose square tends
to zero itself tends to zero, without continuity of the chosen branch. -/
theorem tendsto_zero_of_sq_tendsto_zero {X : Type*} {l : Filter X}
    (Q : X → ℂ) (hQ : Tendsto (fun x => Q x^2) l (𝓝 0)) :
    Tendsto Q l (𝓝 0) := by
  have hn : Tendsto (fun x => Real.sqrt ‖Q x^2‖) l (𝓝 0) := by
    have hnorm : Tendsto (fun x => ‖Q x^2‖) l (𝓝 (0:ℝ)) := by
      simpa only [Function.comp_def,norm_zero] using (continuous_norm.tendsto (0:ℂ)).comp hQ
    simpa only [Function.comp_def,norm_zero,Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0:ℝ)).comp hnorm
  have hpoint : (fun x => Real.sqrt ‖Q x^2‖) = fun x => ‖Q x‖ := by
    funext x
    rw [norm_pow,Real.sqrt_sq (norm_nonneg _)]
  rw [hpoint] at hn
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

end NLS.ComplexAnalysis
