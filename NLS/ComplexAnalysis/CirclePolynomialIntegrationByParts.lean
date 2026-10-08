import NLS.ComplexAnalysis.CircleIntegralIntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Polynomial integration by parts around a closed circle -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

/-- Polynomial weights on a closed contour; analyticity is needed only near the circle. -/
theorem circleIntegral_pow_mul_deriv_eq_neg
    (f : ℂ → ℂ) (D : Set ℂ) (hf : AnalyticOnNhd ℂ f D)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (hc : sphere c R ⊆ D) (k : ℕ) :
    (∮ z in C(c,R), z^(k+1) * deriv f z) =
      -(k+1 : ℂ) * ∮ z in C(c,R), z^k * f z := by
  have hcont : ContinuousOn f (sphere c R) := (hf.continuousOn).mono hc
  have hdcont : ContinuousOn (deriv f) (sphere c R) := (hf.deriv.continuousOn).mono hc
  have hd (z : ℂ) (hz : z ∈ sphere c R) :
      HasDerivAt (fun w => w^(k+1)*f w) ((k+1 : ℂ)*z^k*f z+z^(k+1)*deriv f z) z := by
    simpa only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,id_eq,Pi.pow_apply,mul_one] using!
      ((hasDerivAt_id z).pow (k+1)).mul (hf z (hc hz)).differentiableAt.hasDerivAt
  have hzero : (∮ z in C(c,R), (k+1 : ℂ)*z^k*f z+z^(k+1)*deriv f z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR
    intro z hz
    exact (hd z hz).hasDerivWithinAt
  have hi := (((continuousOn_const (c := (k+1 : ℂ))).mul (continuousOn_id.pow k)).mul hcont).circleIntegrable hR
  have hdi := ((continuousOn_id.pow (k+1)).mul hdcont).circleIntegrable hR
  change CircleIntegrable (fun z : ℂ => (k+1 : ℂ)*z^k*f z) c R at hi
  change CircleIntegrable (fun z : ℂ => z^(k+1)*deriv f z) c R at hdi
  rw [circleIntegral.integral_add hi hdi] at hzero
  simp only [mul_assoc,circleIntegral.integral_const_mul] at hzero
  exact (eq_neg_of_add_eq_zero_right hzero).trans (neg_mul _ _).symm

end NLS.ComplexAnalysis
