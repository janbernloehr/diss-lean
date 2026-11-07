import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! Evaluating a full Banach derivative through a continuous linear target map. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {𝕜 A B C : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B] [NormedAddCommGroup C] [NormedSpace 𝕜 C]

theorem fderiv_comp_clm_apply (F : A → B) (L : B →L[𝕜] C) (x h : A)
    (hF : DifferentiableAt 𝕜 F x) :
    (fderiv 𝕜 (fun q => L (F q)) x) h=L ((fderiv 𝕜 F x) h) := by
  have hd := (L.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  change fderiv 𝕜 (fun q => L (F q)) x = _ at hd
  rw [hd]
  rfl

end NLS.FunctionalAnalysis
