import Mathlib.Analysis.Normed.Operator.Basic

/-! Operator bounds on complete normed-space structures, for use with
iterated physical-real subspaces and their inherited module instances. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem norm_clm_apply_le_of_norm_le (L : E →L[𝕜] F) (x : E) (C : ℝ) (hx : ‖x‖ ≤ C) :
    ‖L x‖ ≤ ‖L‖*C := L.le_opNorm_of_le hx

end NLS.FunctionalAnalysis
