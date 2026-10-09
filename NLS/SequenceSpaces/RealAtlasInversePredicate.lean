import NLS.SequenceSpaces.SourcePropositionI4RealCore
import NLS.ComplexAnalysis.LinearCoordinatesLocalInverse

/-! # Real inverse loci as actual inverse germs -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {f : nonnegativeLocus p → Coeff p} {U : Set (nonnegativeLocus p)}

/-- The original cone value is the center of the restricted extension. -/
theorem NonnegativeAnalyticAtlas.realRestriction_center
    (a : NonnegativeAnalyticAtlas f U) {x : nonnegativeLocus p} (hx : x ∈ U) :
    realRestriction (a.extension x) (reCLM p x.val) = reCLM p (f x) := by
  change reCLM p (a.extension x (RealCoeff.complexCLM p (reCLM p x.val))) = _
  rw [RealCoeff.complexCLM_reCLM p _ (fun n => (x.property n).1),
    ← (a.agreement x hx).eq_of_nhds]

/-- The real inverse locus is exactly the locus of inverse germs of the real restriction. -/
theorem NonnegativeAnalyticAtlas.realLocalInversePoints_eq_germs
    (a : NonnegativeAnalyticAtlas f U) :
    a.realLocalInversePoints = {x ∈ U | ComplexAnalysis.HasAnalyticInverse (𝕜 := ℝ)
      (realRestriction (a.extension x)) (reCLM p x.val)} := by
  ext x
  change (x ∈ U ∧ _) ↔ (x ∈ U ∧ _)
  apply and_congr_right
  intro hx
  dsimp [ComplexAnalysis.HasAnalyticInverse]
  rw [a.realRestriction_center hx]

end NLS.Coeff
