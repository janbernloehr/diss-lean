import NLS.SequenceSpaces.WeightedNonnegativeAnalyticAtlas
import NLS.SequenceSpaces.WeightedRealCoeff
import NLS.SequenceSpaces.SourcePropositionI4RealCore
import NLS.SequenceSpaces.NonnegativeAtlasCoordinates

/-! # Normalized coordinates for weighted cone atlases -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {w : Weight} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {f : nonnegativeLocus w p → WeightedCoeff w p} {U : Set (nonnegativeLocus w p)}

/-- Compatibility of cone coordinates with the continuous linear weighting map. -/
theorem nonnegativeHomeomorph_symm_val_linear (y : Coeff.nonnegativeLocus p) :
    ((nonnegativeHomeomorph w p).symm y).val =
      (weightIsometry w p).toContinuousLinearEquiv.symm y.val := rfl

/-- Weight both the input and output of each local extension. -/
def NonnegativeAnalyticAtlas.toCoeff (a : NonnegativeAnalyticAtlas f U) :
    Coeff.NonnegativeAnalyticAtlas
      (fun y => (weightIsometry w p).toContinuousLinearEquiv (f ((nonnegativeHomeomorph w p).symm y)))
      ((nonnegativeHomeomorph w p).symm ⁻¹' U) :=
  Coeff.NonnegativeAnalyticAtlas.ofCoordinates
    (weightIsometry w p).toContinuousLinearEquiv (nonnegativeHomeomorph w p) Subtype.val
    (nonnegativeHomeomorph_symm_val_linear (w := w)) f U a.extension a.analyticAt a.agreement

/-- The normalized derivative is conjugate to the original weighted derivative. -/
theorem NonnegativeAnalyticAtlas.toCoeff_derivative
    (a : NonnegativeAnalyticAtlas f U) {x : nonnegativeLocus w p} (hx : x ∈ U) :
    a.toCoeff.derivative (nonnegativeHomeomorph w p x) =
      (weightIsometry w p).toContinuousLinearEquiv.conjContinuousAlgEquiv (a.derivative x) := by
  change fderiv ℂ (fun z => (weightIsometry w p).toContinuousLinearEquiv
      (a.extension ((nonnegativeHomeomorph w p).symm (nonnegativeHomeomorph w p x))
        (((weightIsometry w p).toContinuousLinearEquiv).symm z))) ((weightIsometry w p).toContinuousLinearEquiv x.val) = _
  rw [Homeomorph.symm_apply_apply]
  exact ComplexAnalysis.fderiv_linear_conjugate (weightIsometry w p).toContinuousLinearEquiv
    (a.analyticAt x hx).differentiableAt

/-- Original compactness hypotheses suffice in normalized coordinates. -/
theorem NonnegativeAnalyticAtlas.toCoeff_compact
    (a : NonnegativeAnalyticAtlas f U)
    (hc : ∀ x ∈ U, IsCompactOperator (a.derivative x-1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p)) :
    ∀ y ∈ (nonnegativeHomeomorph w p).symm ⁻¹' U,
      IsCompactOperator (a.toCoeff.derivative y-1 : Coeff p →L[ℂ] Coeff p) :=
  Coeff.compact_family_in_coordinates (weightIsometry w p).toContinuousLinearEquiv
    (nonnegativeHomeomorph w p) (fun _ hx => a.toCoeff_derivative hx) hc

/-- Real original values give real normalized values. -/
theorem NonnegativeAnalyticAtlas.toCoeff_real
    (_a : NonnegativeAnalyticAtlas f U) (hr : ∀ x ∈ U, f x ∈ realLocus w p) :
    ∀ y ∈ (nonnegativeHomeomorph w p).symm ⁻¹' U,
      (weightIsometry w p).toContinuousLinearEquiv (f ((nonnegativeHomeomorph w p).symm y)) ∈ Coeff.realLocus p :=
  Coeff.range_predicate_in_coordinates (weightIsometry w p).toContinuousLinearEquiv
    (nonnegativeHomeomorph w p) (mem_realLocus_iff w p) hr

end NLS.WeightedCoeff
