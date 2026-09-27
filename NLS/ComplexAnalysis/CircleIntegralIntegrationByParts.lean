import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Integration by parts on a closed circle

The circle integral of the derivative of `z * f z` vanishes. This
turns the weighted integral of `f'` into the negative unweighted
integral of `f`, without requiring `f` to be analytic inside the
circle.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

/-- Closed-circle integration by parts for a holomorphic function
defined near the circle. The circle may enclose singularities. -/
theorem circleIntegral_mul_deriv_eq_neg
    (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hf : ∀ z ∈ sphere c R, DifferentiableAt ℂ f z)
    (hi : CircleIntegrable f c R)
    (hdi : CircleIntegrable (fun z => z * deriv f z) c R) :
    (∮ z in C(c,R), z * deriv f z) =
      -(∮ z in C(c,R), f z) := by
  have hfun : id * f = (fun w : ℂ => w * f w) := by
    funext w
    rfl
  have hzero : (∮ z in C(c,R),
      deriv (fun w : ℂ => w * f w) z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR
    intro z hz
    have hprod : HasDerivAt (fun w : ℂ => w * f w)
        (f z + z * deriv f z) z := by
      rw [← hfun]
      simpa using ((hasDerivAt_id z).mul ((hf z hz).hasDerivAt))
    simpa [hprod.deriv] using hprod.hasDerivWithinAt
  have hpoint (z : ℂ) (hz : z ∈ sphere c R) :
      deriv (fun w : ℂ => w * f w) z = f z + z * deriv f z := by
    rw [← hfun]
    simpa using ((hasDerivAt_id z).mul ((hf z hz).hasDerivAt)).deriv
  have hsum : (∮ z in C(c,R), f z + z * deriv f z) = 0 := by
    rw [← hzero]
    apply circleIntegral.integral_congr hR
    intro z hz
    exact (hpoint z hz).symm
  rw [circleIntegral.integral_add hi hdi] at hsum
  exact eq_neg_of_add_eq_zero_right hsum

/-- Analyticity on an open neighborhood of the circle supplies all
integrability and differentiability hypotheses for integration by
parts. No extension through the disc is needed. -/
theorem circleIntegral_mul_deriv_eq_neg_of_analyticOnNhd
    (f : ℂ → ℂ) (D : Set ℂ)
    (hf : AnalyticOnNhd ℂ f D)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ D) :
    (∮ z in C(c,R), z * deriv f z) =
      -(∮ z in C(c,R), f z) := by
  have hcont : ContinuousOn f (sphere c R) := by
    intro z hz
    exact ((hf z (hcircle hz)).continuousAt).continuousWithinAt
  have hcont_deriv : ContinuousOn (deriv f) (sphere c R) := by
    intro z hz
    exact ((hf.deriv z (hcircle hz)).continuousAt).continuousWithinAt
  have hi : CircleIntegrable f c R :=
    hcont.circleIntegrable hR
  have hdi : CircleIntegrable (fun z => z * deriv f z) c R :=
    (continuousOn_id.mul hcont_deriv).circleIntegrable hR
  exact circleIntegral_mul_deriv_eq_neg f c R hR
    (fun z hz => (hf z (hcircle hz)).differentiableAt) hi hdi

end NLS.ComplexAnalysis
