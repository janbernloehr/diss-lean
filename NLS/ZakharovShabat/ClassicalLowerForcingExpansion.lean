import NLS.ZakharovShabat.ClassicalScalarForcingLowerKernel

/-! # The lower forcing response with its first kernel correction

A quadratic lower-kernel error controls the actual scalar response after retaining the explicit mass-primitive oscillatory correction.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- A quadratic lower-kernel error gives a quadratic response error after
retaining the explicit mass correction to the free oscillatory integral. -/
theorem norm_classical_lower_forcing_first_order_error_le
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (r P : ℝ → ℂ)
    (hr : Continuous r) (hP : Continuous P) (w : ℂ) (C E : ℝ)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (t : Icc (0:ℝ) 1)
    (hfree : ∀ x ∈ Icc (0:ℝ) 1, ‖exp (-I*z*x)‖ ≤ E)
    (hkernel : ∀ x ∈ Icc (0:ℝ) 1,
      ‖classicalScalarForcingLowerKernel Φ z t x-
        exp (I*z*(t.val-x))*(1+w*(P t-P x))‖ ≤ C*‖w‖^2) :
    ‖(classicalForcedKernelSolution Φ
        (classicalScalarForcing (fun x => exp (-I*z*x)*r x) (by fun_prop)) z t).2-
      exp (I*z*t.val)*(∫ x in (0:ℝ)..t.val, r x*exp (-2*I*z*x))-
      w*exp (I*z*t.val)*(P t*(∫ x in (0:ℝ)..t.val, r x*exp (-2*I*z*x))-
        (∫ x in (0:ℝ)..t.val, P x*r x*exp (-2*I*z*x)))‖ ≤
      C*E*‖w‖^2*(∫ x in (0:ℝ)..1, ‖r x‖) := by
  let F (x : ℝ) := classicalScalarForcingLowerKernel Φ z t x*(exp (-I*z*x)*r x)
  let G (x : ℝ) := exp (I*z*t.val)*(r x*exp (-2*I*z*x))
  let J (x : ℝ) := exp (I*z*t.val)*((P t-P x)*r x*exp (-2*I*z*x))
  have hF : Continuous F := (continuous_classicalScalarForcingLowerKernel Φ z t).mul (by fun_prop)
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hJ : Continuous J := by dsimp [J]; fun_prop
  have hFG : Continuous (fun x => F x-G x) := hF.sub hG
  have hwJ : Continuous (fun x => w*J x) := continuous_const.mul hJ
  have hGi : (∫ x in (0:ℝ)..t.val, G x) =
      exp (I*z*t.val)*(∫ x in (0:ℝ)..t.val, r x*exp (-2*I*z*x)) :=
    intervalIntegral.integral_const_mul _ _
  have hJi : (∫ x in (0:ℝ)..t.val, J x) =
      exp (I*z*t.val)*(P t*(∫ x in (0:ℝ)..t.val, r x*exp (-2*I*z*x))-
        (∫ x in (0:ℝ)..t.val, P x*r x*exp (-2*I*z*x))) := by
    have heq : J = fun x => exp (I*z*t.val)*(P t*(r x*exp (-2*I*z*x))-
        P x*r x*exp (-2*I*z*x)) := by funext x; dsimp [J]; ring
    have h₁ : IntervalIntegrable (fun x : ℝ => P t*(r x*exp (-2*I*z*x))) volume 0 t.val :=
      (by fun_prop : Continuous _).intervalIntegrable _ _
    have h₂ : IntervalIntegrable (fun x : ℝ => P x*r x*exp (-2*I*z*x)) volume 0 t.val :=
      (by fun_prop : Continuous _).intervalIntegrable _ _
    rw [heq,intervalIntegral.integral_const_mul,intervalIntegral.integral_sub h₁ h₂,
      intervalIntegral.integral_const_mul]
  rw [classicalScalarForcing_snd_eq_lowerKernel_integral]
  change ‖(∫ x in (0:ℝ)..t.val, F x)-_ - _‖ ≤ _
  rw [← hGi,show w*exp (I*z*t.val)*(P t*(∫ x in (0:ℝ)..t.val, r x*exp (-2*I*z*x))-
        (∫ x in (0:ℝ)..t.val, P x*r x*exp (-2*I*z*x))) =
      w*(exp (I*z*t.val)*(P t*(∫ x in (0:ℝ)..t.val, r x*exp (-2*I*z*x))-
        (∫ x in (0:ℝ)..t.val, P x*r x*exp (-2*I*z*x)))) by ring,← hJi,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hF.intervalIntegrable _ _) (hG.intervalIntegrable _ _),
    ← intervalIntegral.integral_sub (hFG.intervalIntegrable _ _)
      (hwJ.intervalIntegrable _ _)]
  apply norm_integral_unit_le_mul_integral_norm _ ((hF.sub hG).sub hwJ)
    r hr (C*E*‖w‖^2) (by positivity) _ t
  intro x hx
  have he₁ : exp (I*z*((t.val:ℂ)-x)) = exp (I*z*t.val)*exp (-I*z*x) := by
    rw [← exp_add]
    congr 1
    ring
  have he₂ : exp (-2*I*z*(x:ℂ)) = exp (-I*z*x)*exp (-I*z*x) := by
    rw [← exp_add]
    congr 1
    ring
  have hid : F x-G x-w*J x =
      (classicalScalarForcingLowerKernel Φ z t x-
        exp (I*z*(t.val-x))*(1+w*(P t-P x)))*exp (-I*z*x)*r x := by
    dsimp only [F,G,J]
    rw [he₁,he₂]
    ring
  change ‖F x-G x-w*J x‖ ≤ _
  rw [hid,norm_mul,norm_mul]
  have hh := mul_le_mul (hkernel x hx) (hfree x hx) (norm_nonneg _) (by positivity)
  exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (by ring)

end NLS.ZakharovShabat
