import NLS.ZakharovShabat.SourceBoundaryContours
import NLS.ZakharovShabat.SourceBoundaryRootSpaces

/-!
# Boundary contour ranges lie in the original operator domain

Every projected vector has a representative in the original one-derivative
boundary domain. Restricting the input of either projector to this domain
therefore leaves its whole range unchanged, as in the displayed restrictions
in the proof of Theorem 1.4. In particular their ranks are the same.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_sourceBoundaryDomain_of_preimage (b : BoundaryCondition)
    (x : sourceBoundaryBaseSubspace (p := p) b) (f : Domain p)
    (hf : domainInclusion f = CoeffPair.toMax p x.val) :
    ∃ a : sourceWeightedBoundarySubspace (p := p) b 1, sourceBoundaryInclusion b a = x := by
  have hfb : f ∈ b.domain := (b.inclusion_mem f).mp (hf ▸ x.property)
  refine ⟨(sourceBoundaryDomainEquiv b).symm ⟨f,hfb⟩,?_⟩
  apply (sourceBoundaryBaseEquiv b).injective
  rw [sourceBoundaryBaseEquiv_inclusion,ContinuousLinearEquiv.apply_symm_apply]
  exact Subtype.ext hf

/-- The circle projection takes values in the original weighted boundary domain. -/
theorem sourceBoundaryCircleProjection_exists_domain (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) (x : sourceBoundaryBaseSubspace (p := p) b) :
    ∃ a : sourceWeightedBoundarySubspace (p := p) b 1,
      sourceBoundaryInclusion b a = sourceBoundaryCircleProjection b hp φ c r x := by
  apply exists_sourceBoundaryDomain_of_preimage b _
    (resolventCircleIntegralToDomain hp (CoeffPair.toMax p φ) c r (CoeffPair.toMax p x.val))
  rw [sourceBoundaryCircleProjection_apply b hp φ hφ c r hr hc,
    sourceResolventCircleIntegral_eq_conj hp φ c r hr hc]
  change _ = CoeffPair.toMax p ((CoeffPair.toMax p).symm _)
  rw [ContinuousLinearEquiv.apply_symm_apply,
    resolventCircleIntegral_eq_inclusion hp (CoeffPair.toMax p φ) c r hr
      (by rwa [sourceResolventSet_eq] at hc)]
  rfl

/-- The rectangle projection takes values in the original weighted boundary domain. -/
theorem sourceBoundaryCentralProjection_exists_domain (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) (x : sourceBoundaryBaseSubspace (p := p) b) :
    ∃ a : sourceWeightedBoundarySubspace (p := p) b 1,
      sourceBoundaryInclusion b a = sourceBoundaryCentralProjection b hp φ N x := by
  apply exists_sourceBoundaryDomain_of_preimage b _
    (resolventRectangleIntegralToDomain hp (CoeffPair.toMax p φ) (centralLowerCorner N) (centralUpperCorner N)
      (CoeffPair.toMax p x.val))
  rw [sourceBoundaryCentralProjection_apply b hp φ hφ N hc,
    sourceCentralRectangleIntegral_eq_conj hp φ N hc]
  change _ = CoeffPair.toMax p ((CoeffPair.toMax p).symm _)
  rw [ContinuousLinearEquiv.apply_symm_apply,
    centralRectangleIntegral_eq_inclusion hp (CoeffPair.toMax p φ) N
      (by rwa [sourceResolventSet_eq] at hc)]
  rfl

/-- A projection whose range lies in the domain retains its range upon domain restriction. -/
theorem range_sourceBoundaryProjection_comp_inclusion (b : BoundaryCondition)
    (A : sourceBoundaryBaseSubspace (p := p) b →L[ℂ] sourceBoundaryBaseSubspace (p := p) b)
    (hA : IsIdempotentElem A)
    (hlift : ∀ x, ∃ a : sourceWeightedBoundarySubspace (p := p) b 1, sourceBoundaryInclusion b a = A x) :
    (A.comp (sourceBoundaryInclusion b)).range = A.range := by
  ext x
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨sourceBoundaryInclusion b a,ha⟩
  · rintro ⟨y,hy⟩
    obtain ⟨a,ha⟩ := hlift y
    refine ⟨a,?_⟩
    change A (sourceBoundaryInclusion b a) = x
    rw [ha]
    exact (DFunLike.congr_fun hA y).trans hy

/-- The printed restriction to the one-derivative input domain retains the circle range. -/
theorem range_sourceBoundaryCircleProjection_comp_inclusion (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    ((sourceBoundaryCircleProjection b hp φ c r).comp (sourceBoundaryInclusion b)).range =
      (sourceBoundaryCircleProjection b hp φ c r).range :=
  range_sourceBoundaryProjection_comp_inclusion b _
    (sourceBoundaryCircleProjection_properties b hp φ hφ c r hr hc).1
    (sourceBoundaryCircleProjection_exists_domain b hp φ hφ c r hr hc)

/-- The printed restriction to the one-derivative input domain retains the rectangle range. -/
theorem range_sourceBoundaryCentralProjection_comp_inclusion (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    ((sourceBoundaryCentralProjection b hp φ N).comp (sourceBoundaryInclusion b)).range =
      (sourceBoundaryCentralProjection b hp φ N).range :=
  range_sourceBoundaryProjection_comp_inclusion b _
    (sourceBoundaryCentralProjection_properties b hp φ hφ N hc).1
    (sourceBoundaryCentralProjection_exists_domain b hp φ hφ N hc)

end NLS.ZakharovShabat
