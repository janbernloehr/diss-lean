import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! Restrict a Frechet derivative at the origin along a bounded linear
source map, without unfolding either concrete source realization. -/
noncomputable section
open scoped Topology
namespace NLS.FunctionalAnalysis
variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem fderiv_comp_linear_zero (f : F → G) (L : E →L[𝕜] F)
    (hf : DifferentiableAt 𝕜 f 0) :
    fderiv 𝕜 (fun x => f (L x)) 0 = (fderiv 𝕜 f 0).comp L := by
  have hi : HasFDerivAt f (fderiv 𝕜 f 0) (L 0) := by simpa only [map_zero] using hf.hasFDerivAt
  exact (hi.comp 0 L.hasFDerivAt).fderiv


theorem eventually_comp_linear_zero (L : E →L[𝕜] F) (U : Set F)
    (hU : IsOpen U) (h0 : (0:F) ∈ U) : ∀ᶠ x in 𝓝 (0:E), L x ∈ U := by
  have hL0 : L (0:E) ∈ U := by simpa only [map_zero] using h0
  exact (L.continuous.tendsto (0:E)).eventually (hU.mem_nhds hL0)

end NLS.FunctionalAnalysis
