import NLS.SequenceSpaces.RealAtlasComplexification
import NLS.SequenceSpaces.SourcePropositionI4WeightedReal
import NLS.ComplexAnalysis.LocalInverseGermCongruence

/-! # Local real analytic atlases on the weighted nonnegative cone

The data are real analytic germs on the actual weighted real Banach space.
Holomorphic extensions and their derivative identification are constructed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {w : Weight} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Analyticity on a cone means local extension to real neighborhoods,
including at points with zero coefficients. -/
structure NonnegativeRealAnalyticAtlas (f : nonnegativeLocus w p → WeightedRealCoeff w p)
    (U : Set (nonnegativeLocus w p)) where
  extension : nonnegativeLocus w p → WeightedRealCoeff w p → WeightedRealCoeff w p
  analyticAt : ∀ x ∈ U, AnalyticAt ℝ (extension x) (reCLM w p x.val)
  agreement : ∀ x ∈ U, f =ᶠ[𝓝 x] (fun y => extension x (reCLM w p y.val))

/-- The real inclusion of a cone point is the point itself. -/
theorem nonnegative_real_val (x : nonnegativeLocus w p) :
    (reCLM w p x.val).val = x.val :=
  complexCLM_reCLM w p x.val (fun n => (x.property n).1)

namespace NonnegativeRealAnalyticAtlas
variable {f : nonnegativeLocus w p → WeightedRealCoeff w p} {U : Set (nonnegativeLocus w p)}

/-- Holomorphic extensions constructed from the given real power series. -/
def toComplex (a : NonnegativeRealAnalyticAtlas f U) :
    NonnegativeAnalyticAtlas (fun x => (f x).val) U where
  extension := Coeff.realAtlasComplexExtensions (weightIsometry w p).toContinuousLinearEquiv
    (fun x : nonnegativeLocus w p => reCLM w p x.val) U a.extension a.analyticAt
  analyticAt := fun x hx => by
    simpa only [nonnegative_real_val] using
      Coeff.realAtlasComplexExtensions_analyticAt (weightIsometry w p).toContinuousLinearEquiv
        (fun x : nonnegativeLocus w p => reCLM w p x.val) U a.extension a.analyticAt hx
  agreement := fun x hx => Coeff.realAtlasComplexExtensions_agreement
    (weightIsometry w p).toContinuousLinearEquiv (fun x : nonnegativeLocus w p => reCLM w p x.val)
    ((reCLM w p).continuous.comp continuous_subtype_val) U a.extension a.analyticAt
    (fun x : nonnegativeLocus w p => x.val)
    (fun x : nonnegativeLocus w p => nonnegative_real_val x) a.agreement hx

/-- The constructed complex extension agrees on a full real neighborhood. -/
theorem toComplex_restriction (a : NonnegativeRealAnalyticAtlas f U)
    {x : nonnegativeLocus w p} (hx : x ∈ U) :
    realRestriction (a.toComplex.extension x) =ᶠ[𝓝 (reCLM w p x.val)] a.extension x :=
  Coeff.realAtlasComplexExtensions_restriction (weightIsometry w p).toContinuousLinearEquiv
    (fun x : nonnegativeLocus w p => reCLM w p x.val) U a.extension a.analyticAt hx

/-- Complexification of the derivative of the original real extension. -/
def complexifiedDerivative (a : NonnegativeRealAnalyticAtlas f U) (x : nonnegativeLocus w p) :
    WeightedCoeff w p →L[ℂ] WeightedCoeff w p :=
  Coeff.complexifyRealMap (weightIsometry w p).toContinuousLinearEquiv
    ((realSubmodule w p).subtypeL.comp (fderiv ℝ (a.extension x) (reCLM w p x.val)))

/-- Differentiating the constructed extension recovers the actual real derivative's
complexification, with no derivative compatibility assumption. -/
theorem toComplex_derivative (a : NonnegativeRealAnalyticAtlas f U)
    {x : nonnegativeLocus w p} (hx : x ∈ U) :
    a.toComplex.derivative x = a.complexifiedDerivative x := by
  have h := Coeff.realAtlasComplexExtensions_fderiv (weightIsometry w p).toContinuousLinearEquiv
    (fun x : nonnegativeLocus w p => reCLM w p x.val) U a.extension a.analyticAt hx
  simpa only [nonnegative_real_val,toComplex,NonnegativeAnalyticAtlas.derivative,complexifiedDerivative] using! h

/-- Local real invertibility is defined using the original real extensions. -/
def localInversePoints (a : NonnegativeRealAnalyticAtlas f U) : Set (nonnegativeLocus w p) :=
  {x ∈ U | ComplexAnalysis.HasAnalyticInverse (𝕜 := ℝ)
    (a.extension x) (reCLM w p x.val)}

/-- The constructed complex atlas gives exactly the original real inverse locus. -/
theorem toComplex_realLocalInversePoints (a : NonnegativeRealAnalyticAtlas f U) :
    a.toComplex.realLocalInversePoints = a.localInversePoints := by
  ext x
  change (x ∈ U ∧ _) ↔ (x ∈ U ∧ _)
  exact and_congr_right fun hx => ComplexAnalysis.hasAnalyticInverse_congr_iff (a.toComplex_restriction hx)

/-- The complexified real derivative is intrinsic to the original cone map. -/
theorem complexifiedDerivative_eq (hp : p ≠ ⊤) (a b : NonnegativeRealAnalyticAtlas f U)
    {x : nonnegativeLocus w p} (hx : x ∈ U) :
    a.complexifiedDerivative x = b.complexifiedDerivative x := by
  rw [← a.toComplex_derivative hx,← b.toComplex_derivative hx]
  exact a.toComplex.derivative_eq hp b.toComplex hx

end NonnegativeRealAnalyticAtlas
end NLS.WeightedCoeff
