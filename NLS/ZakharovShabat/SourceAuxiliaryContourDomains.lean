import NLS.ZakharovShabat.SourceAuxiliaryContours
import NLS.ZakharovShabat.SourceAuxiliaryRootSpaces

/-!
# Auxiliary contour ranges lie in the original operator domain

Every projected vector has a representative in the original one-derivative
auxiliary domain. Restricting the input of either projector to this domain
therefore leaves its whole range unchanged, as in the displayed restrictions
in the proof of Proposition 5.2. In particular their ranks are the same.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_sourceAuxiliaryDomain_of_preimage (b : BoundaryCondition)
    (x : auxiliarySourceSpace (p := p) b) (f : Domain p)
    (hf : domainInclusion f = CoeffPair.toMax p x.val) :
    ∃ a : sourceWeightedAuxiliarySubspace (p := p) b 1, sourceAuxiliaryInclusion b a = x := by
  have hfb : f ∈ b.auxiliaryDomain := (b.inclusion_mem_auxiliary f).mp (hf ▸ x.property)
  refine ⟨(sourceAuxiliaryDomainEquiv b).symm ⟨f,hfb⟩,?_⟩
  apply (sourceAuxiliaryBaseEquiv b).injective
  rw [sourceAuxiliaryBaseEquiv_inclusion,ContinuousLinearEquiv.apply_symm_apply]
  exact Subtype.ext hf

/-- The circle projection takes values in the original weighted auxiliary domain. -/
theorem sourceAuxiliaryCircleProjection_exists_domain (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) (x : auxiliarySourceSpace (p := p) b) :
    ∃ a : sourceWeightedAuxiliarySubspace (p := p) b 1,
      sourceAuxiliaryInclusion b a = sourceAuxiliaryCircleProjection b hp φ c r x := by
  apply exists_sourceAuxiliaryDomain_of_preimage b _
    (resolventCircleIntegralToDomain hp (CoeffPair.toMax p φ) c r (CoeffPair.toMax p x.val))
  rw [sourceAuxiliaryCircleProjection_apply b hp φ hφ c r hr hc,
    sourceResolventCircleIntegral_eq_conj hp φ c r hr hc]
  change _ = CoeffPair.toMax p ((CoeffPair.toMax p).symm _)
  rw [ContinuousLinearEquiv.apply_symm_apply,
    resolventCircleIntegral_eq_inclusion hp (CoeffPair.toMax p φ) c r hr
      (by rwa [sourceResolventSet_eq] at hc)]
  rfl

/-- The rectangle projection takes values in the original weighted auxiliary domain. -/
theorem sourceAuxiliaryCentralProjection_exists_domain (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) (x : auxiliarySourceSpace (p := p) b) :
    ∃ a : sourceWeightedAuxiliarySubspace (p := p) b 1,
      sourceAuxiliaryInclusion b a = sourceAuxiliaryCentralProjection b hp φ N x := by
  apply exists_sourceAuxiliaryDomain_of_preimage b _
    (resolventRectangleIntegralToDomain hp (CoeffPair.toMax p φ) (centralLowerCorner N) (centralUpperCorner N)
      (CoeffPair.toMax p x.val))
  rw [sourceAuxiliaryCentralProjection_apply b hp φ hφ N hc,
    sourceCentralRectangleIntegral_eq_conj hp φ N hc]
  change _ = CoeffPair.toMax p ((CoeffPair.toMax p).symm _)
  rw [ContinuousLinearEquiv.apply_symm_apply,
    centralRectangleIntegral_eq_inclusion hp (CoeffPair.toMax p φ) N
      (by rwa [sourceResolventSet_eq] at hc)]
  rfl

/-- A projection whose range lies in the domain retains its range upon domain restriction. -/
theorem range_sourceAuxiliaryProjection_comp_inclusion (b : BoundaryCondition)
    (A : auxiliarySourceSpace (p := p) b →L[ℂ] auxiliarySourceSpace (p := p) b)
    (hA : IsIdempotentElem A)
    (hlift : ∀ x, ∃ a : sourceWeightedAuxiliarySubspace (p := p) b 1, sourceAuxiliaryInclusion b a = A x) :
    (A.comp (sourceAuxiliaryInclusion b)).range = A.range := by
  ext x
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨sourceAuxiliaryInclusion b a,ha⟩
  · rintro ⟨y,hy⟩
    obtain ⟨a,ha⟩ := hlift y
    refine ⟨a,?_⟩
    change A (sourceAuxiliaryInclusion b a) = x
    rw [ha]
    exact (DFunLike.congr_fun hA y).trans hy

/-- The printed restriction to the one-derivative input domain retains the circle range. -/
theorem range_sourceAuxiliaryCircleProjection_comp_inclusion (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    ((sourceAuxiliaryCircleProjection b hp φ c r).comp (sourceAuxiliaryInclusion b)).range =
      (sourceAuxiliaryCircleProjection b hp φ c r).range :=
  range_sourceAuxiliaryProjection_comp_inclusion b _
    (sourceAuxiliaryCircleProjection_properties b hp φ hφ c r hr hc).1
    (sourceAuxiliaryCircleProjection_exists_domain b hp φ hφ c r hr hc)

/-- The printed restriction to the one-derivative input domain retains the rectangle range. -/
theorem range_sourceAuxiliaryCentralProjection_comp_inclusion (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    ((sourceAuxiliaryCentralProjection b hp φ N).comp (sourceAuxiliaryInclusion b)).range =
      (sourceAuxiliaryCentralProjection b hp φ N).range :=
  range_sourceAuxiliaryProjection_comp_inclusion b _
    (sourceAuxiliaryCentralProjection_properties b hp φ hφ N hc).1
    (sourceAuxiliaryCentralProjection_exists_domain b hp φ hφ N hc)

end NLS.ZakharovShabat
