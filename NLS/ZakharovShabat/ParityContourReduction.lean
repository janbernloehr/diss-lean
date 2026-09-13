import NLS.ZakharovShabat.ContourReductionMultiplicity
import NLS.ZakharovShabat.ParityClusterMultiplicity

/-!
# Finite contour reductions in each Fourier parity

For even-supported potentials, the contour range splits into invariant parity
components. Projection transport gives analytic operators on fixed finite
ranges while retaining the original operator-domain restriction.
-/

noncomputable section
open Complex Metric Topology Filter
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The selected Fourier parity of a contour spectral projection. -/
def parityContourProjection (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (R : ℝ) (r : ℤ) :
    PairSpace p →L[ℂ] PairSpace p := pairParityProjection r * resolventCircleIntegral hp φ c R

/-- The parity contour projection is an analytic ambient operator family. -/
theorem analyticAt_parityContourProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (R : ℝ) (r : ℤ) (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) :
    AnalyticAt ℂ (fun ψ => parityContourProjection hp ψ c R r) φ :=
  analyticAt_const.mul (analyticAt_resolventCircleIntegral hp φ c R hR hc)

/-- On even-supported potentials, the parity contour map is idempotent. -/
theorem parityContourProjection_idempotent (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) :
    IsIdempotentElem (parityContourProjection hp φ c R r) := by
  let A := pairParityProjection (p := p) r
  let P := resolventCircleIntegral hp φ c R
  have hAP : A * P = P * A := (pairParityProjection_commute_contour hp φ hφ r c R hR hc).eq
  change (A*P)*(A*P) = A*P
  calc
    _ = A*(P*A)*P := by noncomm_ring
    _ = A*(A*P)*P := by rw [← hAP]
    _ = (A*A)*(P*P) := by noncomm_ring
    _ = A*P := by rw [pairParityProjection_idempotent r, resolventCircleIntegral_idempotent hp φ c R hR hc]

/-- Its range is exactly the parity part of the full spectral range. -/
theorem range_parityContourProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) :
    (parityContourProjection hp φ c R r).range =
      (resolventCircleIntegral hp φ c R).range ⊓ pairParitySubspace r := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    refine ⟨⟨pairParityProjection r y, ?_⟩, pairParityProjection_mem r _⟩
    exact (congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A y)
      (pairParityProjection_commute_contour hp φ hφ r c R hR hc).eq).symm
  · rintro ⟨⟨y,hy⟩,hx⟩
    refine ⟨y,?_⟩
    change pairParityProjection r (resolventCircleIntegral hp φ c R y) = x
    change resolventCircleIntegral hp φ c R y = x at hy
    rw [hy, (pairParityProjection_eq_self_iff r x).mpr hx]

/-- The selected contour range is finite dimensional. -/
theorem finiteDimensional_range_parityContourProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) :
    FiniteDimensional ℂ (parityContourProjection hp φ c R r).range := by
  let := finiteDimensional_range_resolventCircleIntegral hp φ c R hR hc
  rw [range_parityContourProjection hp φ hφ c R r hR hc]
  exact FiniteDimensional.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)

/-- The domain-valued contour lift respects parity, including for distributional potentials. -/
theorem contourLift_parityProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) (x : PairSpace p) :
    resolventCircleIntegralToDomain hp φ c R (pairParityProjection r x) =
      domainParityProjection r (resolventCircleIntegralToDomain hp φ c R x) := by
  apply domainInclusion_injective
  rw [domainInclusion_domainParityProjection]
  have hi (y : PairSpace p) : domainInclusion (resolventCircleIntegralToDomain hp φ c R y) =
      resolventCircleIntegral hp φ c R y :=
    (congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A y)
      (resolventCircleIntegral_eq_inclusion hp φ c R hR hc)).symm
  rw [hi, hi]
  exact (congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A x)
    (pairParityProjection_commute_contour hp φ hφ r c R hR hc).eq).symm

/-- The bounded contour restriction commutes with the fixed Fourier parity projection. -/
theorem pairParityProjection_commute_contourOperator (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) :
    Commute (pairParityProjection r) (contourOperator hp φ c R) := by
  apply ContinuousLinearMap.ext
  intro x
  change pairParityProjection r (operator hp φ (resolventCircleIntegralToDomain hp φ c R x)) =
    operator hp φ (resolventCircleIntegralToDomain hp φ c R (pairParityProjection r x))
  rw [contourLift_parityProjection hp φ hφ c R r hR hc, operator_domainParityProjection hp φ hφ]

/-- The parity spectral projection commutes with the original bounded contour restriction. -/
theorem parityContourProjection_commute_operator (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) :
    Commute (parityContourProjection hp φ c R r) (contourOperator hp φ c R) :=
  (pairParityProjection_commute_contourOperator hp φ hφ c R r hR hc).mul_left
    (contourOperator_commute_projection hp φ c R hR hc)

/-- The parity contour restriction transported to a fixed reference parity range. -/
def reducedParityContourOperator (hp : p ≠ ⊤) (φ ψ : PairSpace p) (c : ℂ) (R : ℝ) (r : ℤ) :
    (parityContourProjection hp φ c R r).range →L[ℂ] (parityContourProjection hp φ c R r).range :=
  ProjectionTransport.compressed (parityContourProjection hp φ c R r)
    (parityContourProjection hp ψ c R r) (contourOperator hp ψ c R)

/-- Transported parity restrictions intertwine the original bounded operator. -/
theorem transport_reducedParityContourOperator (hp : p ≠ ⊤) (φ ψ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (hψ : ψ ∈ pairParitySubspace 0)
    (c : ℂ) (R : ℝ) (r : ℤ) (hR : 0 ≤ R)
    (hcφ : sphere c R ⊆ resolventSet hp φ) (hcψ : sphere c R ⊆ resolventSet hp ψ)
    (hu : IsUnit (ProjectionTransport.transport (parityContourProjection hp φ c R r)
      (parityContourProjection hp ψ c R r))) (x : (parityContourProjection hp φ c R r).range) :
    ProjectionTransport.transport (parityContourProjection hp φ c R r) (parityContourProjection hp ψ c R r)
      (reducedParityContourOperator hp φ ψ c R r x) =
    contourOperator hp ψ c R (ProjectionTransport.transport (parityContourProjection hp φ c R r)
      (parityContourProjection hp ψ c R r) x) :=
  ProjectionTransport.transport_compressed_apply _ _ _
    (parityContourProjection_idempotent hp φ hφ c R r hR hcφ)
    (parityContourProjection_idempotent hp ψ hψ c R r hR hcψ) hu
    (parityContourProjection_commute_operator hp ψ hψ c R r hR hcψ) x

/-- At the reference potential, reduction is the original operator on its parity range. -/
theorem reducedParityContourOperator_self_apply (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ)
    (x : (parityContourProjection hp φ c R r).range) :
    (reducedParityContourOperator hp φ φ c R r x : PairSpace p) = contourOperator hp φ c R x := by
  have ht := ProjectionTransport.transport_self _ (parityContourProjection_idempotent hp φ hφ c R r hR hc)
  have hu : IsUnit (ProjectionTransport.transport (parityContourProjection hp φ c R r)
      (parityContourProjection hp φ c R r)) := by rw [ht]; exact isUnit_one
  simpa only [ht, one_apply_eq_self] using
    transport_reducedParityContourOperator hp φ φ hφ hφ c R r hR hc hc hu x

/-- The fixed-range parity reduction is analytic wherever transport is invertible. -/
theorem analyticAt_reducedParityContourOperator (hp : p ≠ ⊤) (φ ψ : PairSpace p)
    (c : ℂ) (R : ℝ) (r : ℤ) (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp ψ)
    (hu : IsUnit (ProjectionTransport.transport (parityContourProjection hp φ c R r)
      (parityContourProjection hp ψ c R r))) :
    AnalyticAt ℂ (fun θ => reducedParityContourOperator hp φ θ c R r) ψ :=
  ProjectionTransport.analyticAt_compressed _ (analyticAt_parityContourProjection hp ψ c R r hR hc)
    (analyticAt_contourOperator hp ψ c R hR hc) hu

end NLS.ZakharovShabat
