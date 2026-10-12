import NLS.ZakharovShabat.SourceResolvent
import NLS.ZakharovShabat.ContourAnalytic
import NLS.ZakharovShabat.CentralRectangleProjection

/-! # Actual source-norm resolvent contour integrals

These are normalized operator-norm integrals of the original-norm
resolvent. On admissible contours they agree with the conjugated
maximum-product integrals, so their projection properties concern the
actual integrals, including the full central rectangle boundary.
-/
noncomputable section
open Complex Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The positively oriented, normalized circle integral in the original norm. -/
def sourceResolventCircleIntegral (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (r : ℝ) : CoeffPair p →L[ℂ] CoeffPair p :=
  (2*Real.pi*I : ℂ)⁻¹ • ∮ z in C(c,r), sourceResolvent hp φ z

/-- The normalized integral along four oriented rectangle edges. -/
def sourceResolventRectangleIntegral (hp : p ≠ ⊤) (φ : CoeffPair p) (z w : ℂ) : CoeffPair p →L[ℂ] CoeffPair p :=
  (2*Real.pi*I : ℂ)⁻¹ • RectangleIntegral.integral (sourceResolvent hp φ) z w

theorem sourceResolventCircleIntegral_eq_conj (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ sourceResolventSet hp φ) :
    sourceResolventCircleIntegral hp φ c r = (CoeffPair.toMax p).symm.conjContinuousAlgEquiv
      (resolventCircleIntegral hp (CoeffPair.toMax p φ) c r) := by
  have hc' : sphere c r ⊆ resolventSet hp (CoeffPair.toMax p φ) := by
    rwa [sourceResolventSet_eq] at hc
  let A := (CoeffPair.toMax p).symm.conjContinuousAlgEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  change _ = A ((2*Real.pi*I : ℂ)⁻¹ • ∮ z in C(c,r), resolvent hp (CoeffPair.toMax p φ) z)
  rw [map_smul, NLS.CircleIntegral.map A (circleIntegrable_resolvent hp _ c r hr hc')]
  rfl

theorem sourceResolventRectangleIntegral_eq_conj (hp : p ≠ ⊤) (φ : CoeffPair p) (z w : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ sourceResolventSet hp φ) :
    sourceResolventRectangleIntegral hp φ z w = (CoeffPair.toMax p).symm.conjContinuousAlgEquiv
      (resolventRectangleIntegral hp (CoeffPair.toMax p φ) z w) := by
  have hc' : RectangleIntegral.boundary z w ⊆ resolventSet hp (CoeffPair.toMax p φ) := by
    rwa [sourceResolventSet_eq] at hc
  let A := (CoeffPair.toMax p).symm.conjContinuousAlgEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  change _ = A ((2*Real.pi*I : ℂ)⁻¹ • RectangleIntegral.integral (resolvent hp (CoeffPair.toMax p φ)) z w)
  rw [map_smul, RectangleIntegral.map A (rectangleIntegrable_resolvent hp _ z w hc')]
  rfl

theorem sourceResolventCircleIntegral_idempotent (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ sourceResolventSet hp φ) :
    IsIdempotentElem (sourceResolventCircleIntegral hp φ c r) := by
  rw [sourceResolventCircleIntegral_eq_conj hp φ c r hr hc]
  exact (resolventCircleIntegral_idempotent hp _ c r hr
    (by rwa [sourceResolventSet_eq] at hc)).map _

theorem analyticAt_sourceResolventCircleIntegral (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ sourceResolventSet hp φ) :
    AnalyticAt ℂ (fun ψ => sourceResolventCircleIntegral hp ψ c r) φ := by
  have hc' : sphere c r ⊆ resolventSet hp (CoeffPair.toMax p φ) := by
    rwa [sourceResolventSet_eq] at hc
  have ha := ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv.toContinuousLinearEquiv.analyticAt _).comp
    ((analyticAt_resolventCircleIntegral hp _ c r hr hc').comp ((CoeffPair.toMax p).analyticAt φ))
  apply ha.congr
  have hn : ∀ᶠ ψ in nhds φ, CoeffPair.toMax p ψ ∈ resolventCircleDomain hp c r :=
    ((isOpen_resolventCircleDomain hp c r).preimage (CoeffPair.toMax p).continuous).mem_nhds hc'
  filter_upwards [hn] with ψ hψ
  exact (sourceResolventCircleIntegral_eq_conj hp ψ c r hr (by rwa [sourceResolventSet_eq])).symm

theorem isCompactOperator_sourceResolventCircleIntegral (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ sourceResolventSet hp φ) :
    IsCompactOperator (sourceResolventCircleIntegral hp φ c r) := by
  rw [sourceResolventCircleIntegral_eq_conj hp φ c r hr hc]
  change IsCompactOperator ((CoeffPair.toMax p).symm.toContinuousLinearMap ∘
    resolventCircleIntegral hp (CoeffPair.toMax p φ) c r ∘ (CoeffPair.toMax p).toContinuousLinearMap)
  exact ((isCompactOperator_resolventCircleIntegral hp _ c r hr
    (by rwa [sourceResolventSet_eq] at hc)).comp_clm (CoeffPair.toMax p).toContinuousLinearMap).clm_comp
      (CoeffPair.toMax p).symm.toContinuousLinearMap

/-- The actual central rectangular projector from equation (1.4). -/
def sourceCentralRectangleIntegral (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) : CoeffPair p →L[ℂ] CoeffPair p :=
  sourceResolventRectangleIntegral hp φ (centralLowerCorner N) (centralUpperCorner N)

theorem sourceCentralRectangleIntegral_eq_conj (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    sourceCentralRectangleIntegral hp φ N = (CoeffPair.toMax p).symm.conjContinuousAlgEquiv
      (centralRectangleIntegral hp (CoeffPair.toMax p φ) N) :=
  sourceResolventRectangleIntegral_eq_conj hp φ _ _ (by rwa [centralCorner_boundary])

theorem sourceCentralRectangleIntegral_idempotent (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    IsIdempotentElem (sourceCentralRectangleIntegral hp φ N) := by
  rw [sourceCentralRectangleIntegral_eq_conj hp φ N hc]
  exact (centralRectangleIntegral_idempotent hp _ N
    (by rwa [sourceResolventSet_eq] at hc)).map _

theorem isCompactOperator_sourceCentralRectangleIntegral (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    IsCompactOperator (sourceCentralRectangleIntegral hp φ N) := by
  rw [sourceCentralRectangleIntegral_eq_conj hp φ N hc]
  change IsCompactOperator ((CoeffPair.toMax p).symm.toContinuousLinearMap ∘
    centralRectangleIntegral hp (CoeffPair.toMax p φ) N ∘ (CoeffPair.toMax p).toContinuousLinearMap)
  exact ((isCompactOperator_centralRectangleIntegral hp _ N
    (by rwa [sourceResolventSet_eq] at hc)).comp_clm (CoeffPair.toMax p).toContinuousLinearMap).clm_comp
      (CoeffPair.toMax p).symm.toContinuousLinearMap

theorem circleIntegrable_sourceResolvent (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ sourceResolventSet hp φ) :
    CircleIntegrable (sourceResolvent hp φ) c r :=
  ((analyticOnNhd_sourceResolvent hp φ).continuousOn.mono hc).circleIntegrable hr

theorem rectangleIntegrable_sourceResolvent (hp : p ≠ ⊤) (φ : CoeffPair p) (z w : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ sourceResolventSet hp φ) :
    RectangleIntegral.Integrable (sourceResolvent hp φ) z w :=
  RectangleIntegral.integrable_of_continuousOn ((analyticOnNhd_sourceResolvent hp φ).continuousOn.mono hc)

theorem sourceResolventCircleIntegral_apply (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ sourceResolventSet hp φ) (a : CoeffPair p) :
    sourceResolventCircleIntegral hp φ c r a = (2*Real.pi*I : ℂ)⁻¹ • ∮ z in C(c,r), sourceResolvent hp φ z a := by
  rw [sourceResolventCircleIntegral,smul_apply,NLS.CircleIntegral.apply (circleIntegrable_sourceResolvent hp φ c r hr hc)]

theorem sourceResolventRectangleIntegral_apply (hp : p ≠ ⊤) (φ : CoeffPair p) (z w : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ sourceResolventSet hp φ) (a : CoeffPair p) :
    sourceResolventRectangleIntegral hp φ z w a = (2*Real.pi*I : ℂ)⁻¹ • RectangleIntegral.integral (fun ζ => sourceResolvent hp φ ζ a) z w := by
  rw [sourceResolventRectangleIntegral,smul_apply,RectangleIntegral.apply (rectangleIntegrable_sourceResolvent hp φ z w hc)]

/-- A compact idempotent has a finite-dimensional range, identified with
its eigenspace for the nonzero eigenvalue one. -/
private theorem finiteDimensional_sourceProjection_range
    (P : CoeffPair p →L[ℂ] CoeffPair p) (hi : IsIdempotentElem P) (hc : IsCompactOperator P) :
    FiniteDimensional ℂ P.range := by
  have he : P.range = Module.End.eigenspace P.toLinearMap 1 := by
    ext x
    rw [Module.End.mem_eigenspace_iff]
    change (∃ y, P y = x) ↔ P x = (1 : ℂ) • x
    rw [one_smul]
    constructor
    · rintro ⟨y,rfl⟩
      exact DFunLike.congr_fun hi y
    · intro hx
      exact ⟨x,hx⟩
  rw [he]
  exact NLS.CompactSpectrum.finiteDimensional_eigenspace P hc one_ne_zero

/-- The actual original-norm circle projector has finite rank. -/
theorem finiteDimensional_range_sourceResolventCircleIntegral (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ sourceResolventSet hp φ) :
    FiniteDimensional ℂ (sourceResolventCircleIntegral hp φ c r).range :=
  finiteDimensional_sourceProjection_range _
    (sourceResolventCircleIntegral_idempotent hp φ c r hr hc)
    (isCompactOperator_sourceResolventCircleIntegral hp φ c r hr hc)

/-- The actual original-norm central rectangular projector has finite rank. -/
theorem finiteDimensional_range_sourceCentralRectangleIntegral (hp : p ≠ ⊤)
    (φ : CoeffPair p) (N : ℕ) (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    FiniteDimensional ℂ (sourceCentralRectangleIntegral hp φ N).range :=
  finiteDimensional_sourceProjection_range _
    (sourceCentralRectangleIntegral_idempotent hp φ N hc)
    (isCompactOperator_sourceCentralRectangleIntegral hp φ N hc)

end NLS.ZakharovShabat
