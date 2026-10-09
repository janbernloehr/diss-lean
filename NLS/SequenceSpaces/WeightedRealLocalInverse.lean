import NLS.SequenceSpaces.WeightedAnalyticAtlasCoordinates
import NLS.SequenceSpaces.RealAtlasCoordinateGerms

/-! # Actual real inverse germs on the original weighted spaces -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {w : Weight} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {f : nonnegativeLocus w p → WeightedCoeff w p} {U : Set (nonnegativeLocus w p)}

/-- Restrict and project to the genuine real weighted sequence space. -/
abbrev realRestriction (F : WeightedCoeff w p → WeightedCoeff w p) :
    WeightedRealCoeff w p → WeightedRealCoeff w p :=
  Coeff.coordinateRestriction (weightIsometry w p).toContinuousLinearEquiv F

/-- The center of the restricted extension is the original real cone-map value. -/
theorem NonnegativeAnalyticAtlas.realRestriction_center
    (a : NonnegativeAnalyticAtlas f U) {x : nonnegativeLocus w p} (hx : x ∈ U) :
    realRestriction (a.extension x) (reCLM w p x.val) = reCLM w p (f x) := by
  change reCLM w p (a.extension x (WeightedRealCoeff.complexCLM w p (reCLM w p x.val))) = _
  rw [complexCLM_reCLM w p _ (fun n => (x.property n).1),← (a.agreement x hx).eq_of_nhds]

/-- Points with actual two-sided real analytic inverses in the weighted real space. -/
def NonnegativeAnalyticAtlas.realLocalInversePoints (a : NonnegativeAnalyticAtlas f U) :
    Set (nonnegativeLocus w p) :=
  {x ∈ U | ComplexAnalysis.HasAnalyticInverse (𝕜 := ℝ)
    (realRestriction (a.extension x)) (reCLM w p x.val)}

/-- Real inverse germs commute with the weighting coordinates. -/
theorem NonnegativeAnalyticAtlas.mem_realLocalInversePoints_iff_toCoeff
    (a : NonnegativeAnalyticAtlas f U) (x : nonnegativeLocus w p) :
    x ∈ a.realLocalInversePoints ↔ nonnegativeHomeomorph w p x ∈ a.toCoeff.realLocalInversePoints :=
  Coeff.real_inverse_germ_in_coordinates (weightIsometry w p).toContinuousLinearEquiv
    (nonnegativeHomeomorph w p) Subtype.val (nonnegativeHomeomorph_symm_val_linear (w := w))
    f U a.extension a.analyticAt a.agreement x

/-- Compactness and original reality identify the real and complex inverse loci. -/
theorem NonnegativeAnalyticAtlas.realLocalInversePoints_eq
    (hp : p ≠ ⊤) (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hr : ∀ x ∈ U, f x ∈ realLocus w p)
    (hc : ∀ x ∈ U, IsCompactOperator (a.derivative x-1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p)) :
    a.realLocalInversePoints = a.localInversePoints :=
  Coeff.inverse_locus_eq_in_coordinates (weightIsometry w p).toContinuousLinearEquiv
    (nonnegativeHomeomorph w p) a.mem_realLocalInversePoints_iff_toCoeff
    (a.toCoeff.realLocalInversePoints_eq hp
      (hU.preimage (nonnegativeHomeomorph w p).symm.continuous) (a.toCoeff_real hr) (a.toCoeff_compact hc))
    a.localInversePoints_eq a.toCoeff.localInversePoints_eq (fun _ hx => a.toCoeff_derivative hx)

/-- The real inverse locus is intrinsic to the original weighted cone map. -/
theorem NonnegativeAnalyticAtlas.realLocalInversePoints_eq_of_atlas
    (hp : p ≠ ⊤) (a b : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hr : ∀ x ∈ U, f x ∈ realLocus w p)
    (hc : ∀ x ∈ U, IsCompactOperator (a.derivative x-1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p)) :
    a.realLocalInversePoints = b.realLocalInversePoints := by
  have hcb : ∀ x ∈ U, IsCompactOperator (b.derivative x-1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p) := by
    intro x hx
    rw [← a.derivative_eq hp b hx]
    exact hc x hx
  rw [a.realLocalInversePoints_eq hp hU hr hc,b.realLocalInversePoints_eq hp hU hr hcb]
  exact a.localInversePoints_eq_of_atlas hp b

end NLS.WeightedCoeff
