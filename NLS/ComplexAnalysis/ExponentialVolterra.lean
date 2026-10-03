import NLS.ComplexAnalysis.DecayingDuhamelKernel

/-! # Exponential Volterra convolution

Continuity and linearity of the actual integral, together with the inverse
rate bound needed to isolate the first nontrivial discriminant coefficient.
-/
noncomputable section
open Set Complex MeasureTheory intervalIntegral
namespace NLS.ComplexAnalysis

/-- The causal exponential convolution starting at zero. -/
def exponentialVolterra (c : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in 0..t, exp (c * (t - s)) * f s

theorem exponentialVolterra_eq (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    exponentialVolterra c f t = exp (c*t) * ∫ s in 0..t, exp (-c*s) * f s := by
  rw [exponentialVolterra, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [show c * (↑t - ↑s) = c*↑t + -c*↑s by ring, exp_add]
  ring

theorem continuous_exponentialVolterra (c : ℂ) {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (exponentialVolterra c f) := by
  have hi : Continuous (fun t : ℝ => ∫ s in 0..t, exp (-c*s) * f s) :=
    (intervalIntegral.differentiable_integral_of_continuous
      (show Continuous (fun s : ℝ => exp (-c*s) * f s) by fun_prop)).continuous
  have he : exponentialVolterra c f = fun t : ℝ => exp (c*t) * ∫ s in 0..t, exp (-c*s) * f s :=
    funext (exponentialVolterra_eq c f)
  rw [he]
  exact (show Continuous (fun t : ℝ => exp (c*t)) by fun_prop).mul hi

theorem exponentialVolterra_sub (c : ℂ) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    exponentialVolterra c (fun s => f s - g s) t =
      exponentialVolterra c f t - exponentialVolterra c g t := by
  unfold exponentialVolterra
  simp_rw [mul_sub]
  exact intervalIntegral.integral_sub
    ((show Continuous (fun s : ℝ => exp (c*t-c*s)*f s) by fun_prop).intervalIntegrable 0 t)
    ((show Continuous (fun s : ℝ => exp (c*t-c*s)*g s) by fun_prop).intervalIntegrable 0 t)

theorem exponentialVolterra_const_mul (c d : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    exponentialVolterra c (fun s => d * f s) t = d * exponentialVolterra c f t := by
  rw [exponentialVolterra_eq, exponentialVolterra_eq]
  simp_rw [mul_left_comm (exp _) d, intervalIntegral.integral_const_mul]
  ring

theorem norm_exponentialVolterra_le (c : ℂ) (a t M : ℝ) (ha : 0 < a)
    (ht : 0 ≤ t) (hM : 0 ≤ M) (hc : c.re = -a)
    (f : ℝ → ℂ) (hf : ∀ s ∈ Icc 0 t, ‖f s‖ ≤ M) :
    ‖exponentialVolterra c f t‖ ≤ M / a :=
  norm_integral_exp_propagator_mul_le c a t M ha ht hM hc f hf

end NLS.ComplexAnalysis
