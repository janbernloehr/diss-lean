import NLS.ComplexAnalysis.InverseSqrtIntegral
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Curve integrability at square-root singular endpoints

A curve integral is well-defined even when its integrand is singular
at the initial path endpoint, provided its pulled-back one-form grows
no faster than an inverse square root of the path parameter.
-/

noncomputable section
open Set MeasureTheory
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- A square-root weighted bound on the pulled-back complex one-form
implies actual curve integrability at the initial endpoint. -/
theorem curveIntegrable_of_norm_mul_sqrt_parameter_le
    {a b : ℂ} (ω : ℂ → ℂ →L[ℂ] ℂ) (γ : Path a b)
    {d M : ℝ} (hd : 0 < d)
    (hmeas : AEStronglyMeasurable (curveIntegralFun ω γ)
      (volume.restrict (Ioo (0:ℝ) 1)))
    (hbound : ∀ t ∈ Ioo (0:ℝ) 1,
      ‖curveIntegralFun ω γ t * ((Real.sqrt (d*t) : ℝ) : ℂ)‖ ≤ M) :
    CurveIntegrable ω γ := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
  exact integrableOn_Ioo_of_norm_mul_sqrt_mul_le hd (by norm_num) hmeas hbound

end NLS.ComplexAnalysis
