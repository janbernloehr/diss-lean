import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.FunctionalAnalysis.LinearSourceRestrictionDerivative
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! Coordinate derivatives transfer between different weighted Banach
targets when actual coordinates agree on a source neighborhood. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem fderiv_coordinates_comp_linear (w v : Weight)
    (F : E → WeightedCoeff w p) (G : H → WeightedCoeff v q) (L : E →L[ℂ] H)
    (hF : DifferentiableAt ℂ F 0) (hG : DifferentiableAt ℂ G 0)
    (he : ∀ᶠ x in 𝓝 (0:E), ∀ k : ℤ, (F x).val k=(G (L x)).val k) (h : E) (k : ℤ) :
    ((fderiv ℂ F 0) h).val k=((fderiv ℂ G 0) (L h)).val k := by
  have hG0 : HasFDerivAt G (fderiv ℂ G 0) (L 0) := by
    simpa only [map_zero] using hG.hasFDerivAt
  have hleft := (evalCLM w p k).hasFDerivAt.comp 0 hF.hasFDerivAt
  have hright := (evalCLM v q k).hasFDerivAt.comp 0 (hG0.comp 0 L.hasFDerivAt)
  have hscalar : (fun x : E => (G (L x)).val k) =ᶠ[𝓝 (0:E)] (fun x => (F x).val k) := by
    filter_upwards [he] with x hx
    exact (hx k).symm
  have hd := (hleft.congr_of_eventuallyEq hscalar).unique hright
  exact congrArg (fun A : E →L[ℂ] ℂ => A h) hd

end NLS.WeightedCoeff
