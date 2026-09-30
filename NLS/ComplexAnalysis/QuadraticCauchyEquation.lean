import NLS.ComplexAnalysis.CircleCauchyTransformDerivative

/-!
# Cauchy projection preserves the quadratic root equation

The operator `(z-τ)^2-d` times the derivative plus `z-τ` times the
function commutes with interior Cauchy projection. The difference of
the two kernels is a full derivative on the integrating circle. Thus
an annular quotient satisfying the root equation gives an analytic
solution on the whole interior disc, including a collapsed pair.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

def quadraticRootPolynomial (τ d z : ℂ) : ℂ := (z-τ)^2-d

theorem hasDerivAt_quadraticRootPolynomial (τ d z : ℂ) :
    HasDerivAt (quadraticRootPolynomial τ d) (2*(z-τ)) z := by
  convert ((((hasDerivAt_id z).sub_const τ).pow 2).sub_const d) using 1 <;> try rfl
  simp only [id_eq,Nat.cast_ofNat,show (2:ℕ)-1 = 1 from rfl,pow_one,mul_one]

/-- A spectral density satisfying the quadratic root equation near the
circle has an interior Cauchy transform satisfying that same equation.
The right side is analytic throughout the closed disc. -/
theorem circleCauchyTransform_quadratic_equation
    (f g : ℂ → ℂ) (τ d c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (sphere c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (heq : ∀ w ∈ sphere c R,
      quadraticRootPolynomial τ d w*deriv f w+(w-τ)*f w = g w)
    (z : ℂ) (hz : z ∈ ball c R) :
    quadraticRootPolynomial τ d z*deriv (circleCauchyTransform f c R) z +
      (z-τ)*circleCauchyTransform f c R z = g z := by
  have hne (w : ℂ) (hw : w ∈ sphere c R) : w-z ≠ 0 :=
    sub_ne_zero.mpr (fun he => sphere_disjoint_ball.le_bot ⟨he ▸ hw,hz⟩)
  let K : ℂ → ℂ := fun w => quadraticRootPolynomial τ d w*f w/(w-z)
  have hK : AnalyticOnNhd ℂ K (sphere c R) := by
    intro w hw
    have hpoly : AnalyticAt ℂ (quadraticRootPolynomial τ d) w :=
      ((analyticAt_id.sub analyticAt_const).pow 2).sub analyticAt_const
    exact (hpoly.mul (hf w hw)).div (analyticAt_id.sub analyticAt_const) (hne w hw)
  have hKd (w : ℂ) (hw : w ∈ sphere c R) :
      HasDerivAt K
        (((2*(w-τ)*f w+quadraticRootPolynomial τ d w*deriv f w)*(w-z) -
          quadraticRootPolynomial τ d w*f w)/(w-z)^2) w := by
    have hfd : HasDerivAt f (deriv f w) w := (hf w hw).differentiableAt.hasDerivAt
    have hprod : HasDerivAt (fun v => quadraticRootPolynomial τ d v*f v)
        (2*(w-τ)*f w+quadraticRootPolynomial τ d w*deriv f w) w :=
      (hasDerivAt_quadraticRootPolynomial τ d w).fun_mul hfd
    convert hprod.fun_div ((hasDerivAt_id w).sub_const z) (hne w hw) using 1 <;> try rfl
    simp only [id_eq,mul_one]
  have hzero : (∮ w in C(c,R), deriv K w) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR.le
    intro w hw
    exact (hK w hw).differentiableAt.hasDerivAt.hasDerivWithinAt
  have hi1 : CircleIntegrable (fun w => f w/(w-z)) c R := by
    have hc : ContinuousOn (fun w => f w/(w-z)) (sphere c R) :=
      hf.continuousOn.div (continuousOn_id.sub continuousOn_const) hne
    exact hc.circleIntegrable hR.le
  have hi2 : CircleIntegrable (fun w => f w/(w-z)^2) c R := by
    have hc : ContinuousOn (fun w => f w/(w-z)^2) (sphere c R) :=
      hf.continuousOn.div ((continuousOn_id.sub continuousOn_const).pow 2)
        (fun w hw => pow_ne_zero 2 (hne w hw))
    exact hc.circleIntegrable hR.le
  have hid : CircleIntegrable (deriv K) c R := hK.deriv.continuousOn.circleIntegrable hR.le
  have hi1c : CircleIntegrable (fun w => (z-τ)*(f w/(w-z))) c R := hi1.const_mul (z-τ)
  have hi2c : CircleIntegrable (fun w => quadraticRootPolynomial τ d z*(f w/(w-z)^2)) c R :=
    hi2.const_mul (quadraticRootPolynomial τ d z)
  have hisum : CircleIntegrable (fun w => quadraticRootPolynomial τ d z*(f w/(w-z)^2)+
      (z-τ)*(f w/(w-z))) c R := hi2c.add hi1c
  have hidentity (w : ℂ) (hw : w ∈ sphere c R) :
      g w/(w-z) = quadraticRootPolynomial τ d z*(f w/(w-z)^2)+
        (z-τ)*(f w/(w-z))+deriv K w := by
    rw [← heq w hw,(hKd w hw).deriv]
    unfold quadraticRootPolynomial
    field_simp [hne w hw]
    ring
  have hint : (∮ w in C(c,R), g w/(w-z)) =
      quadraticRootPolynomial τ d z*(∮ w in C(c,R), f w/(w-z)^2)+
        (z-τ)*(∮ w in C(c,R), f w/(w-z)) := by
    calc
      _ = ∮ w in C(c,R), quadraticRootPolynomial τ d z*(f w/(w-z)^2)+
          (z-τ)*(f w/(w-z))+deriv K w :=
        circleIntegral.integral_congr hR.le hidentity
      _ = _ := by
        rw [circleIntegral.integral_add hisum hid,
          circleIntegral.integral_add hi2c hi1c,
          circleIntegral.integral_const_mul,circleIntegral.integral_const_mul,hzero,add_zero]
  have hd := hasDerivAt_circleCauchyTransform f c R hR.le hf z
    (fun hs => sphere_disjoint_ball.le_bot ⟨hs,hz⟩)
  have hcauchy := circleIntegral_div_sub_of_differentiable_on_off_countable countable_empty hz
    hg.continuousOn (fun w hw => (hg w (ball_subset_closedBall hw.1)).differentiableAt)
  rw [hint] at hcauchy
  rw [hd.deriv]
  unfold circleCauchyTransform
  have hπ : (2*Real.pi*I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  calc
    _ = (2*Real.pi*I : ℂ)⁻¹ *
        (quadraticRootPolynomial τ d z*(∮ w in C(c,R), f w/(w-z)^2)+
          (z-τ)*(∮ w in C(c,R), f w/(w-z))) := by ring
    _ = g z := by rw [hcauchy,← mul_assoc,inv_mul_cancel₀ hπ,one_mul]

end NLS.ComplexAnalysis
