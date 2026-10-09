import NLS.SequenceSpaces.RealAnalyticGermChoice

/-! # Complexifying families of local real analytic extensions -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {E S : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Choose complex extensions locally; outside the stated domain their values are irrelevant. -/
def realAtlasComplexExtensions (L : E ≃L[ℂ] Coeff p) (j : S → coordinateRealSubmodule L)
    (U : Set S) (F : S → coordinateRealSubmodule L → coordinateRealSubmodule L)
    (ha : ∀ x ∈ U, AnalyticAt ℝ (F x) (j x)) : S → E → E := by
  classical
  exact fun x => if hx : x ∈ U then realGermComplexExtension L (ha x hx) else 0

/-- Holomorphicity of every chosen local extension. -/
theorem realAtlasComplexExtensions_analyticAt (L : E ≃L[ℂ] Coeff p)
    (j : S → coordinateRealSubmodule L) (U : Set S)
    (F : S → coordinateRealSubmodule L → coordinateRealSubmodule L)
    (ha : ∀ x ∈ U, AnalyticAt ℝ (F x) (j x)) {x : S} (hx : x ∈ U) :
    AnalyticAt ℂ (realAtlasComplexExtensions L j U F ha x) (j x).val := by
  simpa only [realAtlasComplexExtensions,dif_pos hx] using realGermComplexExtension_analyticAt L (ha x hx)

/-- Full real-germ agreement retained by the chosen family. -/
theorem realAtlasComplexExtensions_realAgreement (L : E ≃L[ℂ] Coeff p)
    (j : S → coordinateRealSubmodule L) (U : Set S)
    (F : S → coordinateRealSubmodule L → coordinateRealSubmodule L)
    (ha : ∀ x ∈ U, AnalyticAt ℝ (F x) (j x)) {x : S} (hx : x ∈ U) :
    (fun y : coordinateRealSubmodule L => realAtlasComplexExtensions L j U F ha x y.val) =ᶠ[𝓝 (j x)]
      (fun y => (F x y).val) := by
  simpa only [realAtlasComplexExtensions,dif_pos hx] using realGermComplexExtension_agreement L (ha x hx)

/-- Restricting the chosen family recovers the given real local extensions. -/
theorem realAtlasComplexExtensions_restriction (L : E ≃L[ℂ] Coeff p)
    (j : S → coordinateRealSubmodule L) (U : Set S)
    (F : S → coordinateRealSubmodule L → coordinateRealSubmodule L)
    (ha : ∀ x ∈ U, AnalyticAt ℝ (F x) (j x)) {x : S} (hx : x ∈ U) :
    coordinateRestriction L (realAtlasComplexExtensions L j U F ha x) =ᶠ[𝓝 (j x)] F x := by
  simpa only [realAtlasComplexExtensions,dif_pos hx] using realGermComplexExtension_restriction L (ha x hx)

/-- Identification of the actual complexified real derivatives throughout the domain. -/
theorem realAtlasComplexExtensions_fderiv (L : E ≃L[ℂ] Coeff p)
    (j : S → coordinateRealSubmodule L) (U : Set S)
    (F : S → coordinateRealSubmodule L → coordinateRealSubmodule L)
    (ha : ∀ x ∈ U, AnalyticAt ℝ (F x) (j x)) {x : S} (hx : x ∈ U) :
    fderiv ℂ (realAtlasComplexExtensions L j U F ha x) (j x).val =
      complexifyRealMap L ((coordinateRealSubmodule L).subtypeL.comp (fderiv ℝ (F x) (j x))) := by
  simpa only [realAtlasComplexExtensions,dif_pos hx] using realGermComplexExtension_fderiv L (ha x hx)

variable [TopologicalSpace S]

/-- Real-domain agreement pulls back to the original parameter domain. -/
theorem realAtlasComplexExtensions_agreement (L : E ≃L[ℂ] Coeff p)
    (j : S → coordinateRealSubmodule L) (hj : Continuous j) (U : Set S)
    (F : S → coordinateRealSubmodule L → coordinateRealSubmodule L)
    (ha : ∀ x ∈ U, AnalyticAt ℝ (F x) (j x))
    (i : S → E) (hi : ∀ y, (j y).val = i y) {f : S → coordinateRealSubmodule L}
    (he : ∀ x ∈ U, f =ᶠ[𝓝 x] (fun y => F x (j y))) {x : S} (hx : x ∈ U) :
    (fun y => (f y).val) =ᶠ[𝓝 x] (fun y => realAtlasComplexExtensions L j U F ha x (i y)) := by
  have hreal := (realAtlasComplexExtensions_realAgreement L j U F ha hx).comp_tendsto hj.continuousAt
  filter_upwards [he x hx,hreal] with y hy hyr
  change realAtlasComplexExtensions L j U F ha x (j y).val = (F x (j y)).val at hyr
  rw [hy,← hi y]
  exact hyr.symm

end NLS.Coeff
