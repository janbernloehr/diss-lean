import NLS.SequenceSpaces.Weighted
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear

/-! Exact analytic pullback from normalized coefficients to the ORIGINAL
weighted Banach norm. Abstract weights retain the weighting isometry as a
single bounded map, without expanding a concrete spectral weight in proofs. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ComplexAnalysis

theorem analyticOnNhd_comp_linearEquiv
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (e : E ≃L[ℂ] F) (f : F → G) (U : Set F) (hf : AnalyticOnNhd ℂ f U) :
    AnalyticOnNhd ℂ (fun a => f (e a)) (e ⁻¹' U) :=
  hf.comp (e.analyticOnNhd _) (fun _a ha => ha)

theorem exists_analytic_coordinate_pullback
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (e : E ≃L[ℂ] NLS.Coeff 1) (C : Set E) (D U : Set (NLS.Coeff 1))
    (coord : G → ℤ → ℂ) (ω : NLS.Coeff 1 → ℤ → ℂ) (f : NLS.Coeff 1 → G)
    (hCD : ∀ a∈C, e a∈D) (hU : IsOpen U) (hDU : D⊆U)
    (hf : AnalyticOnNhd ℂ f U)
    (hzero : ∀ a : NLS.Coeff 1, ∀ j : ℤ, j≤0 → coord (f a) j=0)
    (hrec : ∀ a∈D, ∀ j : ℤ, coord (f a) j=ω a j) :
    ∃ V : Set E, ∃ g : E → G, IsOpen V ∧ C⊆V ∧ AnalyticOnNhd ℂ g V ∧
      (∀ a : E, ∀ j : ℤ, j≤0 → coord (g a) j=0) ∧
      ∀ a∈C, ∀ j : ℤ, coord (g a) j=ω (e a) j := by
  exact ⟨e ⁻¹' U,(fun a => f (e a)),hU.preimage e.continuous,
    (fun a ha => hDU (hCD a ha)),analyticOnNhd_comp_linearEquiv e f U hf,
    (fun a j hj => hzero _ j hj),(fun a ha => hrec _ (hCD a ha))⟩

end NLS.ComplexAnalysis

namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem analyticOnNhd_comp_weightIsometry (w v : Weight)
    (F : Coeff p → WeightedCoeff v q) (U : Set (Coeff p))
    (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℂ (fun a : WeightedCoeff w p => F (weightIsometry w p a))
      ((weightIsometry w p) ⁻¹' U) :=
  NLS.ComplexAnalysis.analyticOnNhd_comp_linearEquiv
    (weightIsometry w p).toContinuousLinearEquiv F U hF

end NLS.WeightedCoeff
