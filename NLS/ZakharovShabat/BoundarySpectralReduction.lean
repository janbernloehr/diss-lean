import NLS.ZakharovShabat.BoundaryCounting
import NLS.ZakharovShabat.SpectralReduction
import NLS.FunctionalAnalysis.ProjectionTrace

/-!
# Boundary contour lifts and bounded spectral restrictions

The boundary circle projector lifts into the weighted boundary domain. Applying
the original unbounded operator through this lift gives a bounded analytic
operator, supported on the boundary spectral range. These are the operators
whose rank-one traces yield the simple eigenvalues in Lemma 4.5.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

/-- The ambient boundary contour lifted into the one-derivative domain. -/
def contourLift (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) :
    PairSpace p →L[ℂ] Domain p := (domainProjection b).comp (resolventCircleIntegralToDomain hp φ c r)

theorem contourLift_mem (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) (x : PairSpace p) :
    contourLift b hp φ c r x ∈ domain b := domainProjection_mem b _

/-- The same lift, with the actual weighted boundary domain as its codomain. -/
def contourLiftToDomain (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) :
    PairSpace p →L[ℂ] domain (p := p) b :=
  (contourLift b hp φ c r).codRestrict (domain b) (contourLift_mem b hp φ c r)

/-- Domain inclusion recovers exactly the boundary contour projector. -/
theorem inclusion_contourLift (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) (x : PairSpace p) :
    domainInclusion (contourLift b hp φ c r x) = contourProjection b hp φ c r x := by
  change domainInclusion (domainProjection b (resolventCircleIntegralToDomain hp φ c r x)) = _
  rw [inclusion_projection]
  have hI := congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A x)
    (resolventCircleIntegral_eq_inclusion hp φ c r hr hc)
  change resolventCircleIntegral hp φ c r x =
    domainInclusion (resolventCircleIntegralToDomain hp φ c r x) at hI
  rw [← hI]
  rfl

/-- The lift is analytic in the stronger, one-derivative norm. -/
theorem analyticAt_contourLift (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    AnalyticAt ℂ (fun ψ => contourLift b hp ψ c r) φ := by
  have hJ := analyticAt_resolventCircleIntegralToDomain hp φ c r hr hc
  exact ((ContinuousLinearMap.compL ℂ (PairSpace p) (Domain p) (Domain p))
    (domainProjection b)).analyticAt _ |>.comp (f := fun ψ => resolventCircleIntegralToDomain hp ψ c r) hJ

/-- Analyticity also holds with the weighted boundary domain itself as codomain. -/
theorem analyticAt_contourLiftToDomain (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    AnalyticAt ℂ (fun ψ => contourLiftToDomain b hp ψ c r) φ := by
  change AnalyticAt ℂ (fun ψ => (domainRetract b).comp (resolventCircleIntegralToDomain hp ψ c r)) φ
  exact ((ContinuousLinearMap.compL ℂ (PairSpace p) (Domain p) ↥(domain (p := p) b))
    (domainRetract b)).analyticAt (𝕜 := ℂ) (E := PairSpace p →L[ℂ] Domain p)
      (F := PairSpace p →L[ℂ] ↥(domain (p := p) b)) _ |>.comp
        (f := fun ψ => resolventCircleIntegralToDomain hp ψ c r)
          (analyticAt_resolventCircleIntegralToDomain hp φ c r hr hc)

/-- Lifting after projection does not alter the lift. -/
theorem contourLift_comp_projection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    (contourLift b hp φ c r).comp (contourProjection b hp φ c r) = contourLift b hp φ c r := by
  apply ContinuousLinearMap.ext
  intro x
  apply domainInclusion_injective
  change domainInclusion (contourLift b hp φ c r (contourProjection b hp φ c r x)) = _
  rw [inclusion_contourLift b hp φ c r hr hc, inclusion_contourLift b hp φ c r hr hc]
  exact DFunLike.congr_fun (contourProjection_idempotent b hp φ hφ c r hr hc).eq x

/-- Periodic domain-valued contour integration intertwines the two boundary projections. -/
theorem periodicContourLift_projection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) (x : PairSpace p) :
    resolventCircleIntegralToDomain hp φ c r (projection b x) = contourLift b hp φ c r x := by
  apply domainInclusion_injective
  rw [inclusion_contourLift b hp φ c r hr hc]
  have hI := congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A (projection b x))
    (resolventCircleIntegral_eq_inclusion hp φ c r hr hc)
  change resolventCircleIntegral hp φ c r (projection b x) =
    domainInclusion (resolventCircleIntegralToDomain hp φ c r (projection b x)) at hI
  rw [← hI]
  exact (DFunLike.congr_fun (projection_commute_contour b hp φ hφ c r hr hc).eq x).symm

/-- The bounded boundary spectral operator is the original operator applied through the domain lift. -/
def contourOperator (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) :
    PairSpace p →L[ℂ] PairSpace p := (operator hp φ).comp (contourLift b hp φ c r)

theorem contourOperator_eq_projection_mul (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) :
    contourOperator b hp φ c r = projection b * ZakharovShabat.contourOperator hp φ c r := by
  apply ContinuousLinearMap.ext
  intro x
  exact (operator_projection b hp φ hφ _).symm

theorem analyticAt_contourOperator (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    AnalyticAt ℂ (fun ψ => contourOperator b hp ψ c r) φ := by
  have hL : AnalyticAt ℂ (operator hp) φ :=
    analyticAt_const.add ((potentialOperatorCLM hp).analyticAt φ)
  exact ((ContinuousLinearMap.compL ℂ (PairSpace p) (Domain p) (PairSpace p)).analyticAt_bilinear _).comp
    (hL.prod (analyticAt_contourLift b hp φ c r hr hc))

theorem projection_commute_periodicContourOperator (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    Commute (projection b) (ZakharovShabat.contourOperator hp φ c r) := by
  apply ContinuousLinearMap.ext
  intro x
  change projection b (operator hp φ (resolventCircleIntegralToDomain hp φ c r x)) =
    operator hp φ (resolventCircleIntegralToDomain hp φ c r (projection b x))
  rw [periodicContourLift_projection b hp φ hφ c r hr hc]
  exact operator_projection b hp φ hφ _

/-- The bounded boundary restriction is supported on the boundary spectral range. -/
theorem contourOperator_mul_projection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    contourOperator b hp φ c r * contourProjection b hp φ c r = contourOperator b hp φ c r := by
  change ((operator hp φ).comp (contourLift b hp φ c r)).comp _ = _
  rw [ContinuousLinearMap.comp_assoc, contourLift_comp_projection b hp φ hφ c r hr hc]
  rfl

/-- The bounded boundary restriction takes values in the same spectral range. -/
theorem projection_mul_contourOperator (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    contourProjection b hp φ c r * contourOperator b hp φ c r = contourOperator b hp φ c r := by
  rw [contourProjection, contourOperator_eq_projection_mul b hp φ hφ]
  have hcomm := (projection_commute_contour b hp φ hφ c r hr hc).eq
  calc
    (projection b * resolventCircleIntegral hp φ c r) *
        (projection b * ZakharovShabat.contourOperator hp φ c r) =
        projection b * (resolventCircleIntegral hp φ c r * projection b) *
          ZakharovShabat.contourOperator hp φ c r := by noncomm_ring
    _ = projection b * (projection b * resolventCircleIntegral hp φ c r) *
          ZakharovShabat.contourOperator hp φ c r := by rw [← hcomm]
    _ = projection b * (resolventCircleIntegral hp φ c r * ZakharovShabat.contourOperator hp φ c r) := by
      rw [← mul_assoc (projection b), projection_idempotent b, mul_assoc]
    _ = _ := by rw [ZakharovShabat.projection_mul_contourOperator hp φ c r hr hc]

theorem contourOperator_commute_projection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    Commute (contourProjection b hp φ c r) (contourOperator b hp φ c r) := by
  show _ * _ = _ * _
  rw [projection_mul_contourOperator b hp φ hφ c r hr hc,
    contourOperator_mul_projection b hp φ hφ c r hr hc]

/-- On an enclosed boundary eigenvector the lift returns the original domain vector. -/
theorem contourLift_apply_eigenvector (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ)
    (hz : z ∈ ball c r) (f : Domain p) (hb : f ∈ domain b)
    (hf : operator hp φ f = z • domainInclusion f) :
    contourLift b hp φ c r (domainInclusion f) = f := by
  have he : f ∈ periodicEigenspace hp φ z := by
    change spectralPencil hp φ z f = 0
    rw [spectralPencil_apply, hf, sub_self]
  apply domainInclusion_injective
  rw [inclusion_contourLift b hp φ c r (pos_of_mem_ball hz).le hc]
  change projection b (resolventCircleIntegral hp φ c r (domainInclusion f)) = _
  rw [resolventCircleIntegral_apply_eigenvector hp φ c z r hc hz f he]
  exact projection_eq_self b ((inclusion_mem b f).mpr hb)

theorem contourOperator_apply_eigenvector (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ)
    (hz : z ∈ ball c r) (f : Domain p) (hb : f ∈ domain b)
    (hf : operator hp φ f = z • domainInclusion f) :
    contourOperator b hp φ c r (domainInclusion f) = z • domainInclusion f := by
  change operator hp φ (contourLift b hp φ c r (domainInclusion f)) = _
  rw [contourLift_apply_eigenvector b hp φ c z r hc hz f hb hf, hf]

end NLS.ZakharovShabat.BoundaryCondition
