import NLS.ZakharovShabat.SpectralReduction
import NLS.FunctionalAnalysis.FiniteSpectralTrace

/-!
# Analytic spectral trace invariants

Traces of the intrinsic contour restriction agree with traces of any local
analytic reduction. First and second traces thus give analytic symmetric
spectral invariants without choosing branches of individual eigenvalues.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The range equivalence conjugates the local reduction to the intrinsic restriction. -/
theorem reducedContourOperator_conjugate (hp : p ≠ ⊤) (φ ψ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hφ : sphere c r ⊆ resolventSet hp φ)
    (hψ : sphere c r ⊆ resolventSet hp ψ) (hu : IsUnit (contourTransport hp φ ψ c r)) :
    let e := ProjectionTransport.rangeEquivalence _ _
      (resolventCircleIntegral_idempotent hp φ c r hr hφ)
      (resolventCircleIntegral_idempotent hp ψ c r hr hψ) hu
    e.toLinearEquiv.conjAlgEquiv ℂ (reducedContourOperator hp φ ψ c r).toLinearMap =
      (reducedContourOperator hp ψ ψ c r).toLinearMap := by
  intro e
  have hW (y : (resolventCircleIntegral hp φ c r).range) :
      (e y : PairSpace p) = contourTransport hp φ ψ c r y :=
    ProjectionTransport.rangeEquivalence_apply _ _ _ _ hu y
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (e (reducedContourOperator hp φ ψ c r (e.symm x)) : PairSpace p) = _
  rw [hW, contourTransport_reduced_apply hp φ ψ c r hr hφ hψ hu,
    ← hW, e.apply_symm_apply]
  exact (reducedContourOperator_self_apply hp ψ c r hr hψ x).symm

/-- Intrinsic trace of a power of the spectral restriction. -/
def contourTracePower (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) (k : ℕ) : ℂ :=
  LinearMap.trace ℂ (resolventCircleIntegral hp φ c r).range
    ((reducedContourOperator hp φ φ c r).toLinearMap ^ k)

/-- Intrinsic traces do not depend on the local reference range used for reduction. -/
theorem contourTracePower_eq_reduced (hp : p ≠ ⊤) (φ ψ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hφ : sphere c r ⊆ resolventSet hp φ)
    (hψ : sphere c r ⊆ resolventSet hp ψ) (hu : IsUnit (contourTransport hp φ ψ c r)) (k : ℕ) :
    contourTracePower hp ψ c r k = LinearMap.trace ℂ (resolventCircleIntegral hp φ c r).range
      ((reducedContourOperator hp φ ψ c r).toLinearMap ^ k) := by
  let e := ProjectionTransport.rangeEquivalence _ _
    (resolventCircleIntegral_idempotent hp φ c r hr hφ)
    (resolventCircleIntegral_idempotent hp ψ c r hr hψ) hu
  have he := reducedContourOperator_conjugate hp φ ψ c r hr hφ hψ hu
  change e.toLinearEquiv.conjAlgEquiv ℂ (reducedContourOperator hp φ ψ c r).toLinearMap = _ at he
  unfold contourTracePower
  rw [← he, ← map_pow, LinearMap.trace_map]

/-- Every spectral power trace is analytic on the admissible-potential domain. -/
theorem analyticAt_contourTracePower (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) (k : ℕ) :
    AnalyticAt ℂ (fun ψ => contourTracePower hp ψ c r k) φ := by
  let : FiniteDimensional ℂ (resolventCircleIntegral hp φ c r).range :=
    finiteDimensional_range_resolventCircleIntegral hp φ c r hr hc
  obtain ⟨U, ho, hφ, _, _, hA, hU⟩ := exists_local_contourReduction hp φ c r hr hc
  have ha := FiniteSpectralTrace.analyticAt_trace ((hA φ hφ).pow k)
  apply ha.congr
  filter_upwards [ho.mem_nhds hφ] with ψ hψ
  simpa only [Pi.pow_apply, ContinuousLinearMap.toLinearMap_pow] using
    (contourTracePower_eq_reduced hp φ ψ c r hr hc (hU ψ hψ).1 (hU ψ hψ).2.1 k).symm

/-- The midpoint trace expression, interpreted as an eigenvalue midpoint at rank two. -/
def contourMidpoint (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) : ℂ :=
  contourTracePower hp φ c r 1 / 2

/-- The squared-gap trace expression for a rank-two contour. -/
def contourSquaredGap (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) : ℂ :=
  2 * contourTracePower hp φ c r 2 - (contourTracePower hp φ c r 1)^2

/-- Analyticity of the symmetric trace expressions, without an eigenvalue labeling. -/
theorem analyticAt_contourMidpoint_and_squaredGap (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    AnalyticAt ℂ (fun ψ => contourMidpoint hp ψ c r) φ ∧
      AnalyticAt ℂ (fun ψ => contourSquaredGap hp ψ c r) φ := by
  have h₁ := analyticAt_contourTracePower hp φ c r hr hc 1
  have h₂ := analyticAt_contourTracePower hp φ c r hr hc 2
  exact ⟨h₁.div_const, (analyticAt_const.mul h₂).sub (h₁.pow 2)⟩

end NLS.ZakharovShabat
