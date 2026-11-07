import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue

/-! Equality of analytic functions from derivative equality on a dense set
and one matching value, in the FULL norm topology. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem fderiv_eq_of_analytic_dense_fderiv_eq (f g : E → F) (S : Set E)
    (hf : ∀ x, AnalyticAt ℝ f x) (hg : ∀ x, AnalyticAt ℝ g x)
    (hS : Dense S) (hD : ∀ x ∈ S, fderiv ℝ f x=fderiv ℝ g x) :
    ∀ x, fderiv ℝ f x=fderiv ℝ g x := by
  have hc : IsClosed {x | fderiv ℝ f x=fderiv ℝ g x} :=
    isClosed_eq (continuous_iff_continuousAt.mpr (fun x => (hf x).fderiv.continuousAt))
      (continuous_iff_continuousAt.mpr (fun x => (hg x).fderiv.continuousAt))
  intro x
  exact (closure_minimal hD hc) (hS x)

theorem eq_of_analytic_dense_fderiv_eq (f g : E → F) (S : Set E)
    (hf : ∀ x, AnalyticAt ℝ f x) (hg : ∀ x, AnalyticAt ℝ g x)
    (hS : Dense S) (hD : ∀ x ∈ S, fderiv ℝ f x=fderiv ℝ g x)
    (x₀ : E) (h₀ : f x₀=g x₀) : f=g := by
  have hc : IsClosed {x | fderiv ℝ f x=fderiv ℝ g x} :=
    isClosed_eq (continuous_iff_continuousAt.mpr (fun x => (hf x).fderiv.continuousAt))
      (continuous_iff_continuousAt.mpr (fun x => (hg x).fderiv.continuousAt))
  have hall : ∀ x, fderiv ℝ f x=fderiv ℝ g x := by
    intro x
    exact (closure_minimal hD hc) (hS x)
  exact eq_of_fderiv_eq (fun x => (hf x).differentiableAt)
    (fun x => (hg x).differentiableAt) hall x₀ h₀

end NLS.FunctionalAnalysis
