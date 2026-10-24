import NLS.ZakharovShabat.FloquetPeriodicFactorRegularity
import NLS.ZakharovShabat.L2FloquetPeriodicMatrix
import NLS.ZakharovShabat.L2WholeLineIntegralEquation

/-! # The original differential equation for periodic Floquet columns -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Module
namespace NLS.ZakharovShabat

/-- The normalized physical pair column, retaining the original component conventions. -/
def l2FloquetPeriodicColumn (u : IntervalPairL2) (z : ℂ) (v : Fin 2 → ℂ)
    (μ : ℂ) : ℝ → ℂ × ℂ := floquetPeriodicFactor μ (l2WholeLineSolution u z v)

/-- The pair column is exactly the corresponding column of the actual
periodic matrix, not a separate abstract representative. -/
theorem l2FloquetPeriodicColumn_eq_matrix_column (u : IntervalPairL2) (z : ℂ)
    (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)) (μ : Fin 2 → ℂ) (j : Fin 2) (t : ℝ) :
    l2FloquetPeriodicColumn u z (b j) (μ j) t =
      (l2FloquetPeriodicMatrix u z b μ t 0 j,l2FloquetPeriodicMatrix u z b μ t 1 j) := rfl

/-- Every normalized original physical column remains locally absolutely continuous. -/
theorem absolutelyContinuousOnInterval_l2FloquetPeriodicColumn (u : IntervalPairL2)
    (z : ℂ) (v : Fin 2 → ℂ) (μ : ℂ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (l2FloquetPeriodicColumn u z v μ) a b :=
  absolutelyContinuousOnInterval_floquetPeriodicFactor μ _ a b
    (absolutelyContinuousOnInterval_l2WholeLineSolution u z v a b)

/-- The original physical ODE acquires exactly the constant logarithmic
correction on each periodic Floquet column. -/
theorem ae_hasDerivAt_l2FloquetPeriodicColumn (u : IntervalPairL2) (z : ℂ)
    (v : Fin 2 → ℂ) (μ : ℂ) :
    ∀ᵐ t : ℝ, HasDerivAt (l2FloquetPeriodicColumn u z v μ)
      (classicalODECoefficient (l2WholeLinePotential u t) z (l2FloquetPeriodicColumn u z v μ t) -
        Complex.log μ • l2FloquetPeriodicColumn u z v μ t) t := by
  filter_upwards [ae_hasDerivAt_l2WholeLineSolution u z v] with t ht
  have hd := hasDerivAt_floquetPeriodicFactor μ (l2WholeLineSolution u z v) _ t ht
  simpa only [l2FloquetPeriodicColumn,floquetPeriodicFactor,map_smul] using! hd

end NLS.ZakharovShabat
