import NLS.KdV.HillWeakGradientMagri

/-! # Literal complex bilinearity of the physical weak Magri integral -/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

theorem hillWeakGradientMagri_smul_left (q : Coeff 2) (c : ℂ)
    (f df : Curve ℂ) (ddf : ℝ → ℂ) (g dg : Curve ℂ) :
    hillWeakGradientMagri q (c • f) (c • df) (fun x => c*ddf x) g dg =
      c*hillWeakGradientMagri q f df ddf g dg := by
  rw [hillWeakGradientMagri,hillWeakGradientMagri,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  change -(c*ddf x)*NLS.LinearVolterra.extend dg x+
    2*hillIntervalPotential q x*((c*NLS.LinearVolterra.extend f x)*NLS.LinearVolterra.extend dg x-
      (c*NLS.LinearVolterra.extend df x)*NLS.LinearVolterra.extend g x) = _
  ring

theorem hillWeakGradientMagri_smul_right (q : Coeff 2) (c : ℂ)
    (f df : Curve ℂ) (ddf : ℝ → ℂ) (g dg : Curve ℂ) :
    hillWeakGradientMagri q f df ddf (c • g) (c • dg) =
      c*hillWeakGradientMagri q f df ddf g dg := by
  rw [hillWeakGradientMagri,hillWeakGradientMagri,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  change -ddf x*(c*NLS.LinearVolterra.extend dg x)+2*hillIntervalPotential q x*
    (NLS.LinearVolterra.extend f x*(c*NLS.LinearVolterra.extend dg x)-
      NLS.LinearVolterra.extend df x*(c*NLS.LinearVolterra.extend g x)) = _
  ring

end NLS.KdV
