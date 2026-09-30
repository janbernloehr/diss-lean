import NLS.ComplexAnalysis.HolomorphicCurveHomotopy

/-!
# Curve integral congruence away from path endpoints

Changing a scalar one-form's values at the initial and terminal
parameters does not affect integrability or its curve integral. This
allows a removable or singular endpoint to use its analytic extension.
-/

noncomputable section
open Set MeasureTheory
namespace NLS.ComplexAnalysis

theorem curveIntegrable_holomorphicOneForm_congr_interior
    (f g : ℂ → ℂ) {a b : ℂ} (γ : Path a b)
    (h : ∀ t ∈ Ioo (0:ℝ) 1, f (γ.extend t) = g (γ.extend t)) :
    CurveIntegrable (holomorphicOneForm f) γ ↔ CurveIntegrable (holomorphicOneForm g) γ := by
  apply intervalIntegrable_congr_uIoo
  rw [uIoo_of_le zero_le_one]
  intro t ht
  rw [curveIntegralFun_def,curveIntegralFun_def,holomorphicOneForm_apply,
    holomorphicOneForm_apply,h t ht]

theorem curveIntegral_holomorphicOneForm_congr_interior
    (f g : ℂ → ℂ) {a b : ℂ} (γ : Path a b)
    (h : ∀ t ∈ Ioo (0:ℝ) 1, f (γ.extend t) = g (γ.extend t)) :
    (∫ᶜ z in γ, holomorphicOneForm f z) = ∫ᶜ z in γ, holomorphicOneForm g z := by
  rw [curveIntegral_def,curveIntegral_def]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro t ht
  rw [curveIntegralFun_def,curveIntegralFun_def,holomorphicOneForm_apply,
    holomorphicOneForm_apply,h t ht]

end NLS.ComplexAnalysis
