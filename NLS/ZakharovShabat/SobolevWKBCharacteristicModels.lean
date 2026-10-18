import NLS.ZakharovShabat.ClassicalCharacteristicColumnBounds
import NLS.ZakharovShabat.SobolevWKBFundamentalColumns

/-! # Uniform WKB models for the scalar spectral functions

The normalized column models give order-(N+1) errors on original Hs balls and horizontal strips, with smooth periodic representatives explicit.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Trace of the two normalized WKB endpoint columns. -/
def nlsWKBDiscriminantModel (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  (nlsWKBFirstColumnModel a b N z 1).1+(nlsWKBSecondColumnModel a b N z 1).2

/-- The actual anti-discriminant combination is the off-diagonal sum. -/
def nlsWKBAntiDiscriminantModel (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  (nlsWKBSecondColumnModel a b N z 1).1+(nlsWKBFirstColumnModel a b N z 1).2

/-- The source-normalized separated characteristic of the WKB endpoint models. -/
def nlsWKBSeparatedCharacteristicModel (θ : BoundaryCondition)
    (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ((nlsWKBSecondColumnModel a b N z 1).2-(nlsWKBFirstColumnModel a b N z 1).1+
    extensionSign θ*((nlsWKBFirstColumnModel a b N z 1).2-
      (nlsWKBSecondColumnModel a b N z 1).1))/(2*I)

/-- One source-ball threshold and one constant control the actual trace,
anti-discriminant, and both separated characteristics to order N+1. -/
theorem exists_uniform_nlsWKB_characteristic_models_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, T ≤ ‖z‖ → |z.im| ≤ H →
        ‖classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z-
          nlsWKBDiscriminantModel a b N z‖ ≤ C*‖(2*I*z)⁻¹‖^(N+1) ∧
        ‖classicalAntiDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z-
          nlsWKBAntiDiscriminantModel a b N z‖ ≤ C*‖(2*I*z)⁻¹‖^(N+1) ∧
        ∀ θ : BoundaryCondition,
          ‖classicalSeparatedCharacteristic θ
            (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z-
            nlsWKBSeparatedCharacteristicModel θ a b N z‖ ≤ C*‖(2*I*z)⁻¹‖^(N+1) := by
  obtain ⟨T,hT,C,hC,h⟩ := exists_uniform_nlsWKB_fundamental_columns_error_bound s N hs hNs R hR H
  refine ⟨T,hT,2*C,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH
  have hc := h ab hab a b ha hb hpa hpb hca hcb z hz hzH ⟨1,⟨zero_le_one,le_rfl⟩⟩
  have hm := norm_classical_characteristic_errors_of_columns
    (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z
    (nlsWKBFirstColumnModel a b N z 1) (nlsWKBSecondColumnModel a b N z 1)
    (C*‖(2*I*z)⁻¹‖^(N+1)) hc.1 hc.2
  simpa only [nlsWKBDiscriminantModel,nlsWKBAntiDiscriminantModel,
    nlsWKBSeparatedCharacteristicModel,mul_assoc] using hm

end NLS.ZakharovShabat
