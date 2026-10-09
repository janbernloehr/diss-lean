import NLS.SequenceSpaces.WeightedNonnegativeActions
import NLS.FunctionalAnalysis.NonnegativeAnalyticFredholm
import NLS.ComplexAnalysis.LocalAnalyticExtensionTransport

/-! # Relative Fredholm density for every positive sequence weight

Only the parameter cone is changed by weighting. The operator range may
be any complex Banach space, so compactness and invertibility concern
the original operators and their original norms throughout the proof.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {S E : Type*} [TopologicalSpace S]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Fredholm density for any parameter space homeomorphic to the cone. -/
theorem open_dense_isUnit_on_homeomorphic_cone
    (hp : p ≠ ⊤) (e : S ≃ₜ nonnegativeLocus p)
    {A : S → E →L[ℂ] E} {U : Set S} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hA : HasLocalAnalyticExtensions (A ∘ e.symm) (e.symm ⁻¹' U)) {c : ℂ} (hc : c ≠ 0)
    (hcompact : ∀ x ∈ U, IsCompactOperator (A x-c • 1 : E →L[ℂ] E))
    (hstart : ∃ x ∈ U, IsUnit (A x)) :
    IsOpen {x ∈ U | IsUnit (A x)} ∧ U ⊆ closure {x ∈ U | IsUnit (A x)} := by
  apply ComplexAnalysis.open_dense_of_homeomorph e
  exact open_dense_isUnit_of_nonnegative_analytic_compact_shift hp
    (hU.preimage e.symm.continuous) (e.symm.isPreconnected_preimage.mpr hconn)
    hA hc (fun x hx => hcompact _ hx) (e.symm.surjective.exists.mp hstart)

end NLS.Coeff

namespace NLS.WeightedCoeff
variable {w : Weight} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Local analytic extensions from the original weighted cone. -/
def HasLocalAnalyticExtensions (f : nonnegativeLocus w p → F)
    (U : Set (nonnegativeLocus w p)) : Prop :=
  ∀ x ∈ U, ∃ g : WeightedCoeff w p → F, AnalyticAt ℂ g x.val ∧
    f =ᶠ[𝓝 x] (fun y => g y.val)

/-- Weighting parameters transports local extensions without changing their values. -/
theorem HasLocalAnalyticExtensions.toCoeff
    {f : nonnegativeLocus w p → F} {U : Set (nonnegativeLocus w p)}
    (hf : HasLocalAnalyticExtensions f U) :
    Coeff.HasLocalAnalyticExtensions (fun x => f ((nonnegativeHomeomorph w p).symm x))
      ((nonnegativeHomeomorph w p).symm ⁻¹' U) := by
  exact ComplexAnalysis.localAnalyticExtensions_transport
    (weightIsometry w p).symm.toContinuousLinearEquiv
    (nonnegativeHomeomorph w p).symm (nonnegativeHomeomorph w p).symm.continuous
    Subtype.val Subtype.val (fun _ => rfl) hf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Relative generic invertibility on the weighted nonnegative cone. This
covers every real Sobolev order and does not compare different norms. -/
theorem open_dense_isUnit_of_nonnegative_analytic_compact_shift
    (hp : p ≠ ⊤) {A : nonnegativeLocus w p → E →L[ℂ] E}
    {U : Set (nonnegativeLocus w p)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hA : HasLocalAnalyticExtensions A U) {c : ℂ} (hc : c ≠ 0)
    (hcompact : ∀ x ∈ U, IsCompactOperator (A x - c • 1 : E →L[ℂ] E))
    (hstart : ∃ x ∈ U, IsUnit (A x)) :
    IsOpen {x ∈ U | IsUnit (A x)} ∧ U ⊆ closure {x ∈ U | IsUnit (A x)} := by
  exact Coeff.open_dense_isUnit_on_homeomorphic_cone hp (nonnegativeHomeomorph w p)
    hU hconn hA.toCoeff hc hcompact hstart

end NLS.WeightedCoeff
