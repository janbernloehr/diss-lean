import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear

/-! Analytic recovery in a stronger Banach norm from the derivative of an
analytic map and bounded linear generator/recovery maps. Works over REAL
and complex fields; no coordinatewise analyticity criterion is used. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {𝕜 E F D G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem analyticAt_derivative_generator_recovery (f : E → F)
    (S A : D →L[𝕜] E) (R : F →L[𝕜] G) (u : D) (hf : AnalyticAt 𝕜 f (S u)) :
    AnalyticAt 𝕜 (fun x => R ((fderiv 𝕜 f (S x)) (A x))) u := by
  have hD := hf.fderiv.comp (S.analyticAt u)
  have hA := A.analyticAt u
  have he := ((ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).analyticAt_bilinear _).comp₂ hD hA
  exact (R.analyticAt _).comp he

end NLS.FunctionalAnalysis
