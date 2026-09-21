import NLS.FunctionalAnalysis.ProjectionTrace
import NLS.FunctionalAnalysis.FiniteSpectralDeterminant

/-!
# Analytic spectral determinants on varying projection ranges
Local projection transport conjugates an invariant finite-dimensional
restriction to a fixed range. Its shifted determinant is intrinsic and
analytic, including where eigenvalues collide or the determinant vanishes.
-/

noncomputable section
open scoped Topology
namespace NLS.ProjectionDeterminant
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The shifted determinant on the actual projection range, with root-minus-parameter orientation. -/
def determinant (P A : E →L[ℂ] E) (z : ℂ) : ℂ :=
  ((ProjectionTrace.restriction P A).toLinearMap-z • 1).det

/-- Projection transport preserves the full determinant and its normalization. -/
theorem determinant_eq_compressed (P Q A : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hu : IsUnit (ProjectionTransport.transport P Q)) (hA : Commute Q A) (z : ℂ) :
    determinant Q A z = ((ProjectionTransport.compressed P Q A).toLinearMap-z • 1).det := by
  let e := ProjectionTransport.rangeEquivalence P Q hP hQ hu
  unfold determinant
  rw [← ProjectionTrace.compressed_conjugate P Q A hP hQ hu hA]
  exact FiniteSpectralDeterminant.shifted_det_conj e.toLinearEquiv _ z

variable [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Analytic commuting finite-rank families have analytic intrinsic shifted determinants. -/
theorem analyticAt_determinant {P A : X → E →L[ℂ] E} {z : X → ℂ} {a : X}
    (hP : AnalyticAt ℂ P a) (hA : AnalyticAt ℂ A a) (hz : AnalyticAt ℂ z a)
    (hp : IsIdempotentElem (P a)) [FiniteDimensional ℂ (P a).range]
    (hnear : ∀ᶠ x in 𝓝 a, IsIdempotentElem (P x) ∧ Commute (P x) (A x)) :
    AnalyticAt ℂ (fun x => determinant (P x) (A x) (z x)) a := by
  have hu : IsUnit (ProjectionTransport.transport (P a) (P a)) := by
    rw [ProjectionTransport.transport_self _ hp]
    exact isUnit_one
  have ht := FiniteSpectralDeterminant.analyticAt_shifted_det
    (ProjectionTransport.analyticAt_compressed (P a) hP hA hu) hz
  apply ht.congr
  filter_upwards [hnear,ProjectionTransport.eventually_isUnit_transport hP hp] with x hx hux
  exact (determinant_eq_compressed (P a) (P x) (A x) hp hx.1 hux hx.2 (z x)).symm

end NLS.ProjectionDeterminant
