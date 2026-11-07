import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Composition

/-! Transport real analyticity through bounded real linear changes
of the source and target Banach models. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]

theorem analyticAt_linearEquiv_transport (S : E ≃L[ℝ] F) (T : G ≃L[ℝ] H)
    (f : F → G) (x : E) (hf : AnalyticAt ℝ f (S x)) :
    AnalyticAt ℝ (fun y : E => T (f (S y))) x := by
  have hS : AnalyticAt ℝ S x := S.analyticAt x
  have hc : AnalyticAt ℝ (fun y : E => f (S y)) x := hf.comp (f := S) hS
  exact (T.analyticAt _).comp (f := fun y : E => f (S y)) hc

end NLS.FunctionalAnalysis
