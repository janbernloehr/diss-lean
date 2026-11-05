import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Complex.Basic

/-! # Pullback of global holomorphic factors by bounded linear coordinates -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis
variable {A B H X : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A bounded linear change of the data variables pulls back a common
open analytic factor domain without changing its recovery quantifiers. -/
theorem exists_analytic_factor_pullback (L : A →L[ℂ] B) (p : X → A) (f : X → H)
    (h : ∃ V : Set B, ∃ F : B → H,
      IsOpen V ∧ (∀ x, L (p x) ∈ V) ∧ AnalyticOnNhd ℂ F V ∧ ∀ x, F (L (p x)) = f x) :
    ∃ V : Set A, ∃ F : A → H,
      IsOpen V ∧ (∀ x, p x ∈ V) ∧ AnalyticOnNhd ℂ F V ∧ ∀ x, F (p x) = f x := by
  obtain ⟨V,F,hV,hall,hF,hrec⟩ := h
  refine ⟨L ⁻¹' V,fun b => F (L b),hV.preimage L.continuous,hall,?_,hrec⟩
  intro b hb
  exact (hF _ hb).comp (L.analyticAt b)

end NLS.ComplexAnalysis
