import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! Evaluating a Banach derivative after a bounded linear source map. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {𝕜 A B C : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B] [NormedAddCommGroup C] [NormedSpace 𝕜 C]

theorem fderiv_clm_comp_apply (F : B → C) (L : A →L[𝕜] B) (x h : A)
    (hF : DifferentiableAt 𝕜 F (L x)) :
    (fderiv 𝕜 (fun q => F (L q)) x) h=(fderiv 𝕜 F (L x)) (L h) := by
  have hd := (hF.hasFDerivAt.comp x L.hasFDerivAt).fderiv
  change fderiv 𝕜 (fun q => F (L q)) x= _ at hd
  rw [hd]
  rfl

end NLS.FunctionalAnalysis
