import NLS.ZakharovShabat.PeriodicCounting
import NLS.FunctionalAnalysis.ProjectionTransport

/-!
# Local analytic reduction to a fixed spectral subspace

The domain-valued contour projection makes `L P` a bounded analytic operator.
Explicit projection transport identifies nearby spectral ranges with one fixed
finite-dimensional range. This constructs the analytic reduction in the proof
of Lemma 3.7 (printed page 27); identifying its traces with the eigenvalue
midpoint and squared gap is a subsequent step.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Applying the unbounded operator to the contour range through its domain lift. -/
def contourOperator (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) :
    PairSpace p →L[ℂ] PairSpace p :=
  (operator hp φ).comp (resolventCircleIntegralToDomain hp φ c r)

/-- The bounded spectral restriction varies analytically in the potential. -/
theorem analyticAt_contourOperator (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    AnalyticAt ℂ (fun ψ => contourOperator hp ψ c r) φ := by
  have hL : AnalyticAt ℂ (operator hp) φ :=
    analyticAt_const.add ((potentialOperatorCLM hp).analyticAt φ)
  exact ((ContinuousLinearMap.compL ℂ (PairSpace p) (Domain p) (PairSpace p)).analyticAt_bilinear _).comp
    (hL.prod (analyticAt_resolventCircleIntegralToDomain hp φ c r hr hc))

/-- The domain lift is unchanged by applying the spectral projection first. -/
theorem resolventCircleIntegralToDomain_comp_projection (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    (resolventCircleIntegralToDomain hp φ c r).comp (resolventCircleIntegral hp φ c r) =
      resolventCircleIntegralToDomain hp φ c r := by
  have hI (x : PairSpace p) :
      domainInclusion (resolventCircleIntegralToDomain hp φ c r x) =
        resolventCircleIntegral hp φ c r x :=
    (congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A x)
      (resolventCircleIntegral_eq_inclusion hp φ c r hr hc)).symm
  apply ContinuousLinearMap.ext
  intro x
  apply domainInclusion_injective
  change domainInclusion (resolventCircleIntegralToDomain hp φ c r
    (resolventCircleIntegral hp φ c r x)) = _
  rw [hI, hI]
  exact congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A x)
    (resolventCircleIntegral_idempotent hp φ c r hr hc)

/-- The projection intertwines the operator with its domain lift. -/
theorem resolventCircleIntegral_apply_operator (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) (f : Domain p) :
    resolventCircleIntegral hp φ c r (operator hp φ f) =
      operator hp φ (resolventCircleIntegralToDomain hp φ c r (domainInclusion f)) := by
  let P := resolventCircleIntegral hp φ c r
  let J := resolventCircleIntegralToDomain hp φ c r
  have hI (x : PairSpace p) : domainInclusion (J x) = P x :=
    (congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A x)
      (resolventCircleIntegral_eq_inclusion hp φ c r hr hc)).symm
  obtain ⟨w, hw⟩ := resolventSet_nonempty hp φ
  have hJR (x : PairSpace p) : J (resolvent hp φ w x) = resolventToDomain hp φ w (P x) := by
    apply domainInclusion_injective
    rw [hI]
    exact congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A x)
      (resolventCircleIntegral_commute_resolvent hp φ c w r hr hc hw).eq
  have hRf : resolvent hp φ w (spectralPencil hp φ w f) = domainInclusion f :=
    congrArg domainInclusion (resolventToDomain_spectralPencil hp φ w hw f)
  have hS : spectralPencil hp φ w (J (domainInclusion f)) = P (spectralPencil hp φ w f) := by
    rw [← hRf, hJR, spectralPencil_resolventToDomain hp φ w hw]
  simp only [spectralPencil_apply, map_sub, map_smul, hI] at hS
  exact (sub_right_inj.mp hS).symm

/-- The bounded spectral restriction vanishes on the projection's kernel. -/
theorem contourOperator_mul_projection (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    contourOperator hp φ c r * resolventCircleIntegral hp φ c r = contourOperator hp φ c r := by
  change ((operator hp φ).comp (resolventCircleIntegralToDomain hp φ c r)).comp _ = _
  rw [ContinuousLinearMap.comp_assoc, resolventCircleIntegralToDomain_comp_projection hp φ c r hr hc]
  rfl

/-- The bounded spectral restriction takes values in the spectral range. -/
theorem projection_mul_contourOperator (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    resolventCircleIntegral hp φ c r * contourOperator hp φ c r = contourOperator hp φ c r := by
  apply ContinuousLinearMap.ext
  intro x
  change resolventCircleIntegral hp φ c r
    (operator hp φ (resolventCircleIntegralToDomain hp φ c r x)) = _
  rw [resolventCircleIntegral_apply_operator hp φ c r hr hc]
  have hI := congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A x)
    (resolventCircleIntegral_eq_inclusion hp φ c r hr hc)
  change resolventCircleIntegral hp φ c r x =
    domainInclusion (resolventCircleIntegralToDomain hp φ c r x) at hI
  rw [← hI]
  have hJ := congrArg (fun A : PairSpace p →L[ℂ] Domain p => A x)
    (resolventCircleIntegralToDomain_comp_projection hp φ c r hr hc)
  change resolventCircleIntegralToDomain hp φ c r (resolventCircleIntegral hp φ c r x) = _ at hJ
  rw [hJ]
  rfl

/-- The spectral projection commutes with the bounded spectral restriction. -/
theorem contourOperator_commute_projection (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    Commute (resolventCircleIntegral hp φ c r) (contourOperator hp φ c r) := by
  show _ * _ = _ * _
  rw [projection_mul_contourOperator hp φ c r hr hc, contourOperator_mul_projection hp φ c r hr hc]

/-- On an enclosed eigenvector, the bounded contour restriction is the original operator. -/
theorem contourOperator_apply_eigenvector (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hc : sphere c r ⊆ resolventSet hp φ)
    (hz : z ∈ ball c r) (f : Domain p) (hf : operator hp φ f = z • domainInclusion f) :
    contourOperator hp φ c r (domainInclusion f) = z • domainInclusion f := by
  have he : f ∈ periodicEigenspace hp φ z := by
    change spectralPencil hp φ z f = 0
    rw [spectralPencil_apply, hf, sub_self]
  have hP := resolventCircleIntegral_apply_eigenvector hp φ c z r hc hz f he
  have hJ : resolventCircleIntegralToDomain hp φ c r (domainInclusion f) = f := by
    apply domainInclusion_injective
    rw [← ContinuousLinearMap.comp_apply, ← resolventCircleIntegral_eq_inclusion hp φ c r
      (pos_of_mem_ball hz).le hc, hP]
  change operator hp φ (resolventCircleIntegralToDomain hp φ c r (domainInclusion f)) = _
  rw [hJ, hf]

/-- Transport from the reference potential's contour range to the varying one. -/
def contourTransport (hp : p ≠ ⊤) (φ ψ : PairSpace p) (c : ℂ) (r : ℝ) :
    PairSpace p →L[ℂ] PairSpace p :=
  ProjectionTransport.transport (resolventCircleIntegral hp φ c r) (resolventCircleIntegral hp ψ c r)

/-- The contour restriction, transported to the fixed range at `φ`. -/
def reducedContourOperator (hp : p ≠ ⊤) (φ ψ : PairSpace p) (c : ℂ) (r : ℝ) :
    (resolventCircleIntegral hp φ c r).range →L[ℂ] (resolventCircleIntegral hp φ c r).range :=
  ProjectionTransport.compressed (resolventCircleIntegral hp φ c r)
    (resolventCircleIntegral hp ψ c r) (contourOperator hp ψ c r)

/-- The actual intertwining identity for the reduced spectral operator. -/
theorem contourTransport_reduced_apply (hp : p ≠ ⊤) (φ ψ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hφ : sphere c r ⊆ resolventSet hp φ)
    (hψ : sphere c r ⊆ resolventSet hp ψ) (hu : IsUnit (contourTransport hp φ ψ c r))
    (x : (resolventCircleIntegral hp φ c r).range) :
    contourTransport hp φ ψ c r (reducedContourOperator hp φ ψ c r x) =
      contourOperator hp ψ c r (contourTransport hp φ ψ c r x) :=
  ProjectionTransport.transport_compressed_apply _ _ _
    (resolventCircleIntegral_idempotent hp φ c r hr hφ)
    (resolventCircleIntegral_idempotent hp ψ c r hr hψ) hu
    (contourOperator_commute_projection hp ψ c r hr hψ) x

/-- At the reference potential the transport is exactly the identity. -/
theorem contourTransport_self (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    contourTransport hp φ φ c r = 1 :=
  ProjectionTransport.transport_self _ (resolventCircleIntegral_idempotent hp φ c r hr hc)

/-- At the reference potential the reduction agrees with the original spectral restriction. -/
theorem reducedContourOperator_self_apply (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ)
    (x : (resolventCircleIntegral hp φ c r).range) :
    (reducedContourOperator hp φ φ c r x : PairSpace p) = contourOperator hp φ c r x := by
  have ht := contourTransport_self hp φ c r hr hc
  have hu : IsUnit (contourTransport hp φ φ c r) := by rw [ht]; exact isUnit_one
  simpa only [ht, one_apply_eq_self] using contourTransport_reduced_apply hp φ φ c r hr hc hc hu x

/-- Local analytic finite-dimensional reduction, with explicit transport and
inverse on one open neighborhood of the reference potential. -/
theorem exists_local_contourReduction (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ φ ∈ U ∧
      AnalyticOnNhd ℂ (fun ψ => contourTransport hp φ ψ c r) U ∧
      AnalyticOnNhd ℂ (fun ψ => Ring.inverse (contourTransport hp φ ψ c r)) U ∧
      AnalyticOnNhd ℂ (fun ψ => reducedContourOperator hp φ ψ c r) U ∧
      ∀ ψ ∈ U, sphere c r ⊆ resolventSet hp ψ ∧ IsUnit (contourTransport hp φ ψ c r) ∧
        Nonempty ((resolventCircleIntegral hp φ c r).range ≃L[ℂ]
          (resolventCircleIntegral hp ψ c r).range) := by
  have hP := resolventCircleIntegral_idempotent hp φ c r hr hc
  have hnear := ProjectionTransport.eventually_isUnit_transport
    (analyticAt_resolventCircleIntegral hp φ c r hr hc) hP
  have hcircle : ∀ᶠ ψ in 𝓝 φ, sphere c r ⊆ resolventSet hp ψ :=
    (isOpen_resolventCircleDomain hp c r).mem_nhds hc
  obtain ⟨U, hU, ho, hφ⟩ := _root_.mem_nhds_iff.mp (hcircle.and hnear)
  refine ⟨U, ho, hφ, ?_, ?_, ?_, ?_⟩
  · intro ψ hψ
    exact ProjectionTransport.analyticAt_transport _
      (analyticAt_resolventCircleIntegral hp ψ c r hr (hU hψ).1)
  · intro ψ hψ
    exact ProjectionTransport.analyticAt_inverse_transport _
      (analyticAt_resolventCircleIntegral hp ψ c r hr (hU hψ).1) (hU hψ).2
  · intro ψ hψ
    exact ProjectionTransport.analyticAt_compressed _
      (analyticAt_resolventCircleIntegral hp ψ c r hr (hU hψ).1)
      (analyticAt_contourOperator hp ψ c r hr (hU hψ).1) (hU hψ).2
  · intro ψ hψ
    refine ⟨(hU hψ).1, (hU hψ).2, ⟨?_⟩⟩
    exact ProjectionTransport.rangeEquivalence _ _ hP
      (resolventCircleIntegral_idempotent hp ψ c r hr (hU hψ).1) (hU hψ).2

end NLS.ZakharovShabat
