import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Derivatives of compatible Banach realizations retain the same
continuous scalar coordinates after a bounded source inclusion. -/
noncomputable section
open Filter Topology
namespace NLS.FunctionalAnalysis
variable {𝕜 D E Y Z G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem clm_fderiv_eq_of_compatible_coordinates (f : E → Y) (g : D → Z)
    (T : D →L[𝕜] E) (ℓ : Y →L[𝕜] G) (m : Z →L[𝕜] G)
    (q : D) (hf : DifferentiableAt 𝕜 f (T q)) (hg : DifferentiableAt 𝕜 g q)
    (he : (fun a => m (g a)) =ᶠ[𝓝 q] (fun a => ℓ (f (T a)))) (h : D) :
    m (fderiv 𝕜 g q h) = ℓ (fderiv 𝕜 f (T q) (T h)) := by
  have hdg := m.hasFDerivAt.comp q hg.hasFDerivAt
  have hdf := ℓ.hasFDerivAt.comp q (hf.hasFDerivAt.comp q T.hasFDerivAt)
  have hh := hdg.unique (hdf.congr_of_eventuallyEq he)
  exact congrArg (fun A : D →L[𝕜] G => A h) hh

end NLS.FunctionalAnalysis
