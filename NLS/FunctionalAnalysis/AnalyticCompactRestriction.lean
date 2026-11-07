import NLS.FunctionalAnalysis.CompactPerturbationEquivalence
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Compact derivative defects and injective derivatives pass to
compatible stronger Banach realizations of the same analytic map. -/
noncomputable section
open Filter Topology
namespace NLS.FunctionalAnalysis
variable {𝕜 E F Y G E₀ F₀ : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
  [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀]

theorem isCompactOperator_fderiv_linear_add_restricted_defect
    (A : E →L[𝕜] F) (I : E →L[𝕜] Y) (Q : G →L[𝕜] F) (R : Y → G) (q : E)
    (hR : DifferentiableAt 𝕜 R (I q)) (hc : IsCompactOperator (fderiv 𝕜 R (I q))) :
    IsCompactOperator (fderiv 𝕜 (fun a => A a+Q (R (I a))) q-A) := by
  have hd := A.hasFDerivAt.add (Q.hasFDerivAt.comp q
    (hR.hasFDerivAt.comp q I.hasFDerivAt))
  have he : fderiv 𝕜 (fun a => A a+Q (R (I a))) q =
      A+Q.comp ((fderiv 𝕜 R (I q)).comp I) := hd.fderiv
  rw [he, add_sub_cancel_left]
  exact (hc.comp_clm I).clm_comp Q

theorem fderiv_injective_of_compatible_inclusions
    (f : E → F) (f₀ : E₀ → F₀) (I : E →L[𝕜] E₀) (J : F →L[𝕜] F₀)
    (hI : Function.Injective I) (he : ∀ a, J (f a) = f₀ (I a)) (q : E)
    (hf : DifferentiableAt 𝕜 f q) (hf₀ : DifferentiableAt 𝕜 f₀ (I q))
    (hinj : Function.Injective (fderiv 𝕜 f₀ (I q))) :
    Function.Injective (fderiv 𝕜 f q) := by
  have hd := J.hasFDerivAt.comp q hf.hasFDerivAt
  have hd₀ := hf₀.hasFDerivAt.comp q I.hasFDerivAt
  have hh := hd.unique (hd₀.congr_of_eventuallyEq (Eventually.of_forall he))
  intro a b hab
  apply hI
  apply hinj
  have ha := congrArg (fun L : E →L[𝕜] F₀ => L a) hh
  have hb := congrArg (fun L : E →L[𝕜] F₀ => L b) hh
  change J (fderiv 𝕜 f q a) = fderiv 𝕜 f₀ (I q) (I a) at ha
  change J (fderiv 𝕜 f q b) = fderiv 𝕜 f₀ (I q) (I b) at hb
  exact ha.symm.trans ((congrArg J hab).trans hb)

end NLS.FunctionalAnalysis
