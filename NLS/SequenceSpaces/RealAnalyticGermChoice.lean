import NLS.SequenceSpaces.RealDerivativeComplexification

/-! # Chosen complex extensions with real-germ and derivative identification -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Choose a holomorphic extension of an actual real analytic germ. -/
def realGermComplexExtension (L : E ≃L[ℂ] Coeff p)
    {f : coordinateRealSubmodule L → coordinateRealSubmodule L} {x : coordinateRealSubmodule L}
    (hf : AnalyticAt ℝ f x) : E → E :=
  (exists_complex_extension_in_coordinates L
    (((coordinateRealSubmodule L).subtypeL.analyticAt (f x)).comp hf)).choose

/-- The chosen extension is holomorphic at the original included real center. -/
theorem realGermComplexExtension_analyticAt (L : E ≃L[ℂ] Coeff p)
    {f : coordinateRealSubmodule L → coordinateRealSubmodule L} {x : coordinateRealSubmodule L}
    (hf : AnalyticAt ℝ f x) : AnalyticAt ℂ (realGermComplexExtension L hf) x.val :=
  (exists_complex_extension_in_coordinates L
    (((coordinateRealSubmodule L).subtypeL.analyticAt (f x)).comp hf)).choose_spec.1

/-- Agreement holds on a whole real neighborhood, including directions outside the cone. -/
theorem realGermComplexExtension_agreement (L : E ≃L[ℂ] Coeff p)
    {f : coordinateRealSubmodule L → coordinateRealSubmodule L} {x : coordinateRealSubmodule L}
    (hf : AnalyticAt ℝ f x) :
    (fun y : coordinateRealSubmodule L => realGermComplexExtension L hf y.val) =ᶠ[𝓝 x]
      (fun y => (f y).val) :=
  (exists_complex_extension_in_coordinates L
    (((coordinateRealSubmodule L).subtypeL.analyticAt (f x)).comp hf)).choose_spec.2

/-- Restricting the chosen extension recovers the original real germ. -/
theorem realGermComplexExtension_restriction (L : E ≃L[ℂ] Coeff p)
    {f : coordinateRealSubmodule L → coordinateRealSubmodule L} {x : coordinateRealSubmodule L}
    (hf : AnalyticAt ℝ f x) : coordinateRestriction L (realGermComplexExtension L hf) =ᶠ[𝓝 x] f := by
  filter_upwards [realGermComplexExtension_agreement L hf] with y hy
  change coordinateReCLM L (realGermComplexExtension L hf y.val) = f y
  rw [hy,coordinateReCLM_val]

/-- The complex derivative is the complexification of the original real derivative. -/
theorem realGermComplexExtension_fderiv (L : E ≃L[ℂ] Coeff p)
    {f : coordinateRealSubmodule L → coordinateRealSubmodule L} {x : coordinateRealSubmodule L}
    (hf : AnalyticAt ℝ f x) :
    fderiv ℂ (realGermComplexExtension L hf) x.val =
      complexifyRealMap L ((coordinateRealSubmodule L).subtypeL.comp (fderiv ℝ f x)) := by
  have hh := fderiv_eq_complexifyRealMap L (realGermComplexExtension_analyticAt L hf)
    (realGermComplexExtension_agreement L hf)
  have hd := ((coordinateRealSubmodule L).subtypeL.hasFDerivAt.comp x hf.differentiableAt.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (f y).val) x = _ at hd
  rwa [hd] at hh

end NLS.Coeff
