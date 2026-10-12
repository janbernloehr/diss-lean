import NLS.ZakharovShabat.SourceContourTrace
import NLS.FunctionalAnalysis.ProjectionTrace

/-! # Local analytic reduction in the original source norms

Explicit projection transport identifies nearby actual contour ranges. The
transported operator acts through the original one-derivative domain lift,
and its traces agree with the intrinsic original-norm traces.
-/
noncomputable section
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceContourOperator_commute_projection (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    Commute (sourceResolventCircleIntegral hp φ c R) (sourceContourOperator hp φ c R) := by
  rw [sourceResolventCircleIntegral_eq_conj hp φ c R hR hc,sourceContourOperator_eq_conj]
  exact (contourOperator_commute_projection hp (CoeffPair.toMax p φ) c R hR
    (by rwa [sourceResolventSet_eq] at hc)).map _

theorem analyticAt_sourceContourOperator (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    AnalyticAt ℂ (fun ψ => sourceContourOperator hp ψ c R) φ := by
  have he : (fun ψ : CoeffPair p => sourceContourOperator hp ψ c R) =
      fun ψ => (CoeffPair.toMax p).symm.conjContinuousAlgEquiv
        (contourOperator hp (CoeffPair.toMax p ψ) c R) := funext (fun ψ => sourceContourOperator_eq_conj hp ψ c R)
  rw [he]
  exact ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv.toContinuousLinearEquiv.analyticAt _).comp
    ((analyticAt_contourOperator hp (CoeffPair.toMax p φ) c R hR
      (by rwa [sourceResolventSet_eq] at hc)).comp ((CoeffPair.toMax p).analyticAt φ))

/-- Ambient transport inducing the local equivalence of original-norm contour ranges. -/
def sourceContourTransport (hp : p ≠ ⊤) (φ ψ : CoeffPair p) (c : ℂ) (R : ℝ) :
    CoeffPair p →L[ℂ] CoeffPair p :=
  ProjectionTransport.transport (sourceResolventCircleIntegral hp φ c R) (sourceResolventCircleIntegral hp ψ c R)

/-- The varying original operator expressed on the fixed reference contour range. -/
def sourceReducedContourOperator (hp : p ≠ ⊤) (φ ψ : CoeffPair p) (c : ℂ) (R : ℝ) :
    (sourceResolventCircleIntegral hp φ c R).range →L[ℂ] (sourceResolventCircleIntegral hp φ c R).range :=
  ProjectionTransport.compressed (sourceResolventCircleIntegral hp φ c R)
    (sourceResolventCircleIntegral hp ψ c R) (sourceContourOperator hp ψ c R)

/-- The transported restriction intertwines the actual original-domain operator. -/
theorem sourceContourTransport_reduced_apply (hp : p ≠ ⊤) (φ ψ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hφ : Metric.sphere c R ⊆ sourceResolventSet hp φ)
    (hψ : Metric.sphere c R ⊆ sourceResolventSet hp ψ) (hu : IsUnit (sourceContourTransport hp φ ψ c R))
    (x : (sourceResolventCircleIntegral hp φ c R).range) :
    sourceContourTransport hp φ ψ c R (sourceReducedContourOperator hp φ ψ c R x) =
      sourceOperator hp ψ (sourceContourLift hp ψ c R (sourceContourTransport hp φ ψ c R x.val)) :=
  ProjectionTransport.transport_compressed_apply _ _ _
    (sourceResolventCircleIntegral_idempotent hp φ c R hR hφ)
    (sourceResolventCircleIntegral_idempotent hp ψ c R hR hψ) hu
    (sourceContourOperator_commute_projection hp ψ c R hR hψ) x

/-- The concrete range isomorphism induced by the invertible source transport. -/
def sourceContourRangeTransport (hp : p ≠ ⊤) (φ ψ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hφ : Metric.sphere c R ⊆ sourceResolventSet hp φ)
    (hψ : Metric.sphere c R ⊆ sourceResolventSet hp ψ) (hu : IsUnit (sourceContourTransport hp φ ψ c R)) :
    (sourceResolventCircleIntegral hp φ c R).range ≃L[ℂ] (sourceResolventCircleIntegral hp ψ c R).range :=
  ProjectionTransport.rangeEquivalence _ _ (sourceResolventCircleIntegral_idempotent hp φ c R hR hφ)
    (sourceResolventCircleIntegral_idempotent hp ψ c R hR hψ) hu

theorem sourceContourRangeTransport_apply (hp : p ≠ ⊤) (φ ψ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hφ : Metric.sphere c R ⊆ sourceResolventSet hp φ)
    (hψ : Metric.sphere c R ⊆ sourceResolventSet hp ψ) (hu : IsUnit (sourceContourTransport hp φ ψ c R))
    (x : (sourceResolventCircleIntegral hp φ c R).range) :
    (sourceContourRangeTransport hp φ ψ c R hR hφ hψ hu x).val = sourceContourTransport hp φ ψ c R x.val :=
  ProjectionTransport.rangeEquivalence_apply _ _ _ _ hu x

/-- The transported vector is represented exactly by its original-domain lift. -/
theorem sourceInclusion_contourLift_transported (hp : p ≠ ⊤) (φ ψ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hφ : Metric.sphere c R ⊆ sourceResolventSet hp φ)
    (hψ : Metric.sphere c R ⊆ sourceResolventSet hp ψ) (hu : IsUnit (sourceContourTransport hp φ ψ c R))
    (x : (sourceResolventCircleIntegral hp φ c R).range) :
    sourceDomainInclusion (sourceContourLift hp ψ c R (sourceContourTransport hp φ ψ c R x.val)) =
      sourceContourTransport hp φ ψ c R x.val := by
  simpa only [sourceContourRangeTransport_apply] using
    sourceInclusion_contourLift_range hp ψ c R hR hψ (sourceContourRangeTransport hp φ ψ c R hR hφ hψ hu x)

/-- Analytic transport, inverse transport, and reduction on one open source neighborhood. -/
theorem exists_local_sourceContourReduction (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      AnalyticOnNhd ℂ (fun ψ => sourceContourTransport hp φ ψ c R) U ∧
      AnalyticOnNhd ℂ (fun ψ => Ring.inverse (sourceContourTransport hp φ ψ c R)) U ∧
      AnalyticOnNhd ℂ (fun ψ => sourceReducedContourOperator hp φ ψ c R) U ∧
      ∀ ψ ∈ U, Metric.sphere c R ⊆ sourceResolventSet hp ψ ∧ IsUnit (sourceContourTransport hp φ ψ c R) ∧
        Nonempty ((sourceResolventCircleIntegral hp φ c R).range ≃L[ℂ]
          (sourceResolventCircleIntegral hp ψ c R).range) := by
  have hP := sourceResolventCircleIntegral_idempotent hp φ c R hR hc
  have hnear := ProjectionTransport.eventually_isUnit_transport
    (analyticAt_sourceResolventCircleIntegral hp φ c R hR hc) hP
  have hcircle : ∀ᶠ ψ in 𝓝 φ, Metric.sphere c R ⊆ sourceResolventSet hp ψ := by
    have hn : ∀ᶠ ψ in 𝓝 φ, CoeffPair.toMax p ψ ∈ resolventCircleDomain hp c R :=
      (((isOpen_resolventCircleDomain hp c R).preimage (CoeffPair.toMax p).continuous).mem_nhds
        (show CoeffPair.toMax p φ ∈ resolventCircleDomain hp c R from by rwa [sourceResolventSet_eq] at hc))
    filter_upwards [hn] with ψ hψ
    rwa [sourceResolventSet_eq]

  obtain ⟨U,hU,ho,hφ⟩ := _root_.mem_nhds_iff.mp (hcircle.and hnear)
  refine ⟨U,ho,hφ,?_,?_,?_,?_⟩
  · intro ψ hψ
    exact ProjectionTransport.analyticAt_transport _
      (analyticAt_sourceResolventCircleIntegral hp ψ c R hR (hU hψ).1)
  · intro ψ hψ
    exact ProjectionTransport.analyticAt_inverse_transport _
      (analyticAt_sourceResolventCircleIntegral hp ψ c R hR (hU hψ).1) (hU hψ).2
  · intro ψ hψ
    exact ProjectionTransport.analyticAt_compressed _
      (analyticAt_sourceResolventCircleIntegral hp ψ c R hR (hU hψ).1)
      (analyticAt_sourceContourOperator hp ψ c R hR (hU hψ).1) (hU hψ).2
  · intro ψ hψ
    exact ⟨(hU hψ).1,(hU hψ).2,⟨ProjectionTransport.rangeEquivalence _ _ hP
      (sourceResolventCircleIntegral_idempotent hp ψ c R hR (hU hψ).1) (hU hψ).2⟩⟩

/-- Intrinsic power traces equal traces of the local analytic reduction. -/
theorem sourceContourTracePower_eq_reduced (hp : p ≠ ⊤) (φ ψ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hφ : Metric.sphere c R ⊆ sourceResolventSet hp φ)
    (hψ : Metric.sphere c R ⊆ sourceResolventSet hp ψ) (hu : IsUnit (sourceContourTransport hp φ ψ c R)) (k : ℕ) :
    sourceContourTracePower hp ψ c R k = LinearMap.trace ℂ (sourceResolventCircleIntegral hp φ c R).range
      ((sourceReducedContourOperator hp φ ψ c R).toLinearMap^k) := by
  have hrest : ProjectionTrace.restriction (sourceResolventCircleIntegral hp ψ c R)
      (sourceContourOperator hp ψ c R) = sourceContourRestriction hp ψ c R := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    rw [ProjectionTrace.restriction_apply _ _ (sourceResolventCircleIntegral_idempotent hp ψ c R hR hψ)
      (sourceContourOperator_commute_projection hp ψ c R hR hψ),sourceContourRestriction_apply hp ψ c R hR hψ]
    rfl
  have he := ProjectionTrace.compressed_conjugate _ _ _
    (sourceResolventCircleIntegral_idempotent hp φ c R hR hφ)
    (sourceResolventCircleIntegral_idempotent hp ψ c R hR hψ) hu
    (sourceContourOperator_commute_projection hp ψ c R hR hψ)
  rw [hrest] at he
  unfold sourceContourTracePower
  rw [← he, ← map_pow, LinearMap.trace_map]
  rfl

/-- Both displayed formulas hold on the fixed reference range, with the source's factor one half. -/
theorem sourceContourMidpoint_halfSquaredGap_eq_reduced (hp : p ≠ ⊤) (φ ψ : CoeffPair p) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hφ : Metric.sphere c R ⊆ sourceResolventSet hp φ)
    (hψ : Metric.sphere c R ⊆ sourceResolventSet hp ψ) (hu : IsUnit (sourceContourTransport hp φ ψ c R))
    (hdim : Module.finrank ℂ (sourceResolventCircleIntegral hp φ c R).range = 2) :
    sourceContourMidpoint hp ψ c R = LinearMap.trace ℂ (sourceResolventCircleIntegral hp φ c R).range
      (sourceReducedContourOperator hp φ ψ c R).toLinearMap / 2 ∧
    LinearMap.trace ℂ (sourceResolventCircleIntegral hp φ c R).range
      (((sourceReducedContourOperator hp φ ψ c R).toLinearMap - sourceContourMidpoint hp ψ c R • 1)^2) =
        sourceContourSquaredGap hp ψ c R / 2 := by
  let := finiteDimensional_range_sourceResolventCircleIntegral hp φ c R hR hφ
  have ht₁ := sourceContourTracePower_eq_reduced hp φ ψ c R hR hφ hψ hu 1
  have ht₂ := sourceContourTracePower_eq_reduced hp φ ψ c R hR hφ hψ hu 2
  simp only [pow_one] at ht₁
  constructor
  · exact congrArg (fun z : ℂ => z/2) ht₁
  · rw [FiniteSpectralTrace.trace_centered_square,hdim,← ht₁,← ht₂]
    simp only [Nat.cast_ofNat]
    unfold sourceContourMidpoint sourceContourSquaredGap
    ring

end NLS.ZakharovShabat
