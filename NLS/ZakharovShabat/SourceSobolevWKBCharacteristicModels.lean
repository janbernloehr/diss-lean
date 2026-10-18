import NLS.ZakharovShabat.SourceSobolevClassicalCompatibility
import NLS.ZakharovShabat.SobolevWKBCharacteristicModels

/-! # WKB estimates for the original source spectral functions

All scalar estimates retain the original Sobolev source and source-normalized canonical spectral functions.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- One source-ball threshold and one constant control the actual trace,
anti-discriminant, and both separated characteristics to order N+1. -/
theorem exists_uniform_source_nlsWKB_characteristic_models_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, T ≤ ‖z‖ → |z.im| ≤ H →
        ‖canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s ab)) z-
          nlsWKBDiscriminantModel a b N z‖ ≤ C*‖(2*I*z)⁻¹‖^(N+1) ∧
        ‖sourceAntiDiscriminantCandidate (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab) z-
          nlsWKBAntiDiscriminantModel a b N z‖ ≤ C*‖(2*I*z)⁻¹‖^(N+1) ∧
        ∀ θ : BoundaryCondition,
          ‖periodOneBoundaryCharacteristic (by norm_num) (by norm_num) θ
            (higherSobolevSourceInclusion s ab) z-
            nlsWKBSeparatedCharacteristicModel θ a b N z‖ ≤ C*‖(2*I*z)⁻¹‖^(N+1) := by
  obtain ⟨T,hT,C,hC,h⟩ := exists_uniform_nlsWKB_characteristic_models_error_bound s N hs hNs R hR H
  refine ⟨T,hT,C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH
  have he := higherSobolev_spectral_functions_eq_classical s hs ab a b
    ha.continuous hb.continuous hpa hpb hca hcb z
  rw [he.1,he.2.1]
  simp only [he.2.2]
  exact h ab hab a b ha hb hpa hpb hca hcb z hz hzH

end NLS.ZakharovShabat
