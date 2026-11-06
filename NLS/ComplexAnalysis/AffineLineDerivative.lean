import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # The actual bounded differential along an affine scalar line -/
noncomputable section
set_option autoImplicit false
namespace NLS.ComplexAnalysis
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem hasDerivAt_comp_affine_line (f : E → F) (x v : E) (hf : DifferentiableAt 𝕜 f x) :
    HasDerivAt (fun c : 𝕜 => f (x+c • v)) ((fderiv 𝕜 f x) v) 0 := by
  have hline : HasDerivAt (fun c : 𝕜 => x+c • v) v 0 := by
    simpa using! ((hasDerivAt_id (0 : 𝕜)).smul_const v).const_add x
  have hd : HasFDerivAt f (fderiv 𝕜 f x) (x+(0 : 𝕜) • v) := by
    simpa only [zero_smul,add_zero] using! hf.hasFDerivAt
  simpa only [Function.comp_def] using! hd.comp_hasDerivAt 0 hline

end NLS.ComplexAnalysis
