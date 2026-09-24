import NLS.ComplexAnalysis.InverseSqrtIntegral
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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

/-- The same square-root bound gives an explicit norm bound for the
improper endpoint curve integral. -/
theorem norm_curveIntegral_le_of_norm_mul_sqrt_parameter_le
    {a b : ℂ} (ω : ℂ → ℂ →L[ℂ] ℂ) (γ : Path a b)
    {d M : ℝ} (hd : 0 < d)
    (hbound : ∀ t ∈ Ioo (0:ℝ) 1,
      ‖curveIntegralFun ω γ t * ((Real.sqrt (d*t) : ℝ) : ℂ)‖ ≤ M) :
    ‖∫ᶜ z in γ, ω z‖ ≤ (M / Real.sqrt d) * 2 := by
  let F := curveIntegralFun ω γ
  let C := M / Real.sqrt d
  let g : ℝ → ℝ := fun t => C * t ^ (-1/2 : ℝ)
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hpoint (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : ‖F t‖ ≤ g t := by
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
    have hdt : 0 < Real.sqrt (d*t) := Real.sqrt_pos.2 (mul_pos hd ht.1)
    have hweight : Real.sqrt t * t ^ (-1/2 : ℝ) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht.1]
      norm_num
    have hprod : Real.sqrt (d*t) * g t = M := by
      rw [Real.sqrt_mul hd.le]
      dsimp [g,C]
      calc
        (Real.sqrt d * Real.sqrt t) *
            ((M / Real.sqrt d) * t ^ (-1/2 : ℝ)) =
          (Real.sqrt d * (M / Real.sqrt d)) *
            (Real.sqrt t * t ^ (-1/2 : ℝ)) := by ring
        _ = M := by
          rw [hweight, mul_one]
          exact mul_div_cancel₀ M hsd.ne'
    have hw : ‖F t‖ * Real.sqrt (d*t) ≤ M := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using hbound t ht
    apply le_of_mul_le_mul_left ?_ hdt
    calc
      Real.sqrt (d*t) * ‖F t‖ = ‖F t‖ * Real.sqrt (d*t) := by ring
      _ ≤ M := hw
      _ = Real.sqrt (d*t) * g t := hprod.symm
  have hg : IntervalIntegrable g volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2
    exact ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 1)).2
      (by norm_num : -1 < (-1/2 : ℝ))).const_mul C
  have hpointae : ∀ᵐ t ∂volume, t ∈ Ioc (0:ℝ) 1 → ‖F t‖ ≤ g t := by
    rw [← ae_restrict_iff' measurableSet_Ioc,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc,
      ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall hpoint
  have hle := intervalIntegral.norm_integral_le_of_norm_le
    zero_le_one hpointae hg
  rw [curveIntegral_def]
  calc
    ‖∫ t in (0:ℝ)..1, F t‖ ≤ ∫ t in (0:ℝ)..1, g t := hle
    _ = C * (∫ t in (0:ℝ)..1, t ^ (-1/2 : ℝ)) := by
      exact intervalIntegral.integral_const_mul C _
    _ = C * 2 := by
      rw [integral_rpow
        (Or.inl (by norm_num : -1 < (-1/2 : ℝ)))]
      norm_num
    _ = (M / Real.sqrt d) * 2 := rfl

end NLS.ComplexAnalysis
