import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic

/-! Exact real restriction of a complex analytic germ through bounded
REAL source inclusion and bounded REAL target projection, with opaque
original Banach spaces and unchanged checking limits. -/
noncomputable section
namespace NLS.ComplexAnalysis

theorem analyticAt_real_linear_transport
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (J : E →L[ℝ] F) (L : G →L[ℝ] H) (f : F → G) (q : E)
    (hf : AnalyticAt ℂ f (J q)) :
    AnalyticAt ℝ (fun p => L (f (J p))) q :=
  (L.analyticAt _).comp (f := fun p => f (J p))
    ((hf.restrictScalars (𝕜 := ℝ)).comp (J.analyticAt q))

end NLS.ComplexAnalysis
