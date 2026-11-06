import NLS.ComplexAnalysis.BanachHolomorphicAnalytic
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! # Conjugating both sides of a complex analytic map

The source and target involutions reverse the complex scalars twice.
Local complex differentiability therefore gives a genuine Banach power
series for the conjugated map, also in infinite-dimensional domains.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
universe u
namespace NLS.ComplexAnalysis
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [StarAddMonoid E] [StarModule ℂ E] [ContinuousStar E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [StarAddMonoid F] [StarModule ℂ F] [ContinuousStar F] [CompleteSpace F]

/-- Conjugating both source and target preserves local complex analyticity. -/
theorem analyticAt_star_star {f : E → F} {x : E} (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (star ∘ f ∘ star) (star x) := by
  let U : Set E := {y | AnalyticAt ℂ f y}
  let V : Set E := star ⁻¹' U
  have hU : IsOpen U := isOpen_analyticAt ℂ f
  have hV : IsOpen V := hU.preimage continuous_star
  have hx : star x ∈ V := by simpa [V,U] using hf
  apply analyticOnNhd_of_complexDifferentiableOn _ V hV _ _ hx
  intro y hy
  have hd := (show AnalyticAt ℂ f (star y) from hy).differentiableAt.star_star
  simpa only [star_star] using hd.differentiableWithinAt (s := V)

end NLS.ComplexAnalysis
