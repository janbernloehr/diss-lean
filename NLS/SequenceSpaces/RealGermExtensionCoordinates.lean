import NLS.SequenceSpaces.RealAnalyticComplexExtension
import NLS.SequenceSpaces.RealCoefficientCoordinates

/-! # Real analytic extensions in original complex coordinates -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real analytic germ on a closed real coefficient subspace extends in the
original complex coordinates, with full real-neighborhood agreement. -/
theorem exists_complex_extension_in_coordinates (L : E ≃L[ℂ] Coeff p)
    {f : coordinateRealSubmodule L → F} {x : coordinateRealSubmodule L}
    (hf : AnalyticAt ℝ f x) :
    ∃ g : E → F, AnalyticAt ℂ g x.val ∧ (fun y : coordinateRealSubmodule L => g y.val) =ᶠ[𝓝 x] f := by
  let e := coordinateRealEquiv L
  have hf' : AnalyticAt ℝ (fun y => f (e.symm y)) (e x) :=
    hf.comp_of_eq (f := e.symm) (e.symm.analyticAt (e x)) (e.symm_apply_apply x)
  obtain ⟨g,hg,he⟩ := Complexification.exists_complex_extension_of_analyticAt hf'
  have hc : RealCoeff.complexCLM p (e x) = L x.val := complex_coordinateRealEquiv L x
  rw [hc] at hg
  refine ⟨fun z => g (L z),hg.comp (L.analyticAt x.val),?_⟩
  filter_upwards [he.comp_tendsto e.continuous.continuousAt] with y hy
  change g (RealCoeff.complexCLM p (e y)) = f (e.symm (e y)) at hy
  rw [e.symm_apply_apply,complex_coordinateRealEquiv] at hy
  exact hy

end NLS.Coeff
