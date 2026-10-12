import NLS.ZakharovShabat.SourceBoundarySpectra
import NLS.ZakharovShabat.SourceContourRanks

/-!
# Original boundary restrictions of the Cauchy–Riesz integrals

The operators here act on the original boundary base spaces. On admissible
contours they are the actual restrictions of the normalized circle and
four-edge rectangle integrals, with range equal to the boundary part of the
ambient range. Continuous range equivalences preserve ranks without assuming
an isometry between the original norm and the auxiliary maximum norm.
-/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complementary boundary projection in the original component-sum norm. -/
def sourceBoundaryProjection (b : BoundaryCondition) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.conjContinuousAlgEquiv (b.projection)

theorem sourceBoundaryProjection_mem (b : BoundaryCondition) (a : CoeffPair p) :
    sourceBoundaryProjection b a ∈ sourceBoundaryBaseSubspace b := by
  change CoeffPair.toMax p ((CoeffPair.toMax p).symm (b.projection (CoeffPair.toMax p a))) ∈ b.space
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact b.projection_mem _

theorem sourceBoundaryProjection_eq_self (b : BoundaryCondition) (a : CoeffPair p)
    (ha : a ∈ sourceBoundaryBaseSubspace b) : sourceBoundaryProjection b a = a := by
  change (CoeffPair.toMax p).symm (b.projection (CoeffPair.toMax p a)) = a
  have he : b.projection (CoeffPair.toMax p a) = CoeffPair.toMax p a := b.projection_eq_self ha
  rw [he, ContinuousLinearEquiv.symm_apply_apply]

private def boundaryGenericCompression {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Submodule ℂ E) (Q : E →L[ℂ] S) :
    (E →L[ℂ] E) →L[ℂ] (S →L[ℂ] S) :=
  ((ContinuousLinearMap.compL ℂ S E S).flip S.subtypeL).comp
    ((ContinuousLinearMap.compL ℂ E E S) Q)

private theorem boundaryGenericCompression_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Submodule ℂ E) (Q : E →L[ℂ] S) (A : E →L[ℂ] E) :
    AnalyticAt ℂ (boundaryGenericCompression S Q) A := ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := E →L[ℂ] E)
    (F := S →L[ℂ] S) (boundaryGenericCompression S Q) A

/-- Bounded compression; for commuting operators this is their actual restriction. -/
def sourceBoundaryCompression (b : BoundaryCondition) :
    (CoeffPair p →L[ℂ] CoeffPair p) →L[ℂ]
      (sourceBoundaryBaseSubspace (p := p) b →L[ℂ] sourceBoundaryBaseSubspace (p := p) b) :=
  boundaryGenericCompression (E := CoeffPair p) (sourceBoundaryBaseSubspace (p := p) b)
    ((sourceBoundaryProjection b).codRestrict _ (sourceBoundaryProjection_mem b))

theorem analyticAt_sourceBoundaryCompression (b : BoundaryCondition) (A : CoeffPair p →L[ℂ] CoeffPair p) :
    AnalyticAt ℂ (sourceBoundaryCompression b) A := boundaryGenericCompression_analytic _ _ A

theorem sourceBoundaryCompression_apply (b : BoundaryCondition) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceBoundaryProjection b) A) (x : sourceBoundaryBaseSubspace (p := p) b) :
    (sourceBoundaryCompression b A x).val = A x.val := by
  change sourceBoundaryProjection b (A x.val) = A x.val
  have h := DFunLike.congr_fun hA.eq x.val
  change sourceBoundaryProjection b (A x.val) = A (sourceBoundaryProjection b x.val) at h
  rw [h, sourceBoundaryProjection_eq_self b x.val x.property]

theorem sourceBoundaryProjection_commute_circleIntegral (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    Commute (sourceBoundaryProjection b) (sourceResolventCircleIntegral hp φ c r) := by
  rw [sourceResolventCircleIntegral_eq_conj hp φ c r hr hc]
  exact (b.projection_commute_contour hp (CoeffPair.toMax p φ) hφ c r hr
    (by rwa [sourceResolventSet_eq] at hc)).map ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv)

/-- The circle integral compressed to the selected original boundary space. -/
def sourceBoundaryCircleProjection (b : BoundaryCondition) (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (r : ℝ) :
    sourceBoundaryBaseSubspace (p := p) b →L[ℂ] sourceBoundaryBaseSubspace (p := p) b :=
  sourceBoundaryCompression b (sourceResolventCircleIntegral hp φ c r)

theorem sourceBoundaryCompression_idempotent (b : BoundaryCondition) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceBoundaryProjection b) A) (hAA : IsIdempotentElem A) :
    IsIdempotentElem (sourceBoundaryCompression b A) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change (sourceBoundaryCompression b A (sourceBoundaryCompression b A x)).val =
    (sourceBoundaryCompression b A x).val
  rw [sourceBoundaryCompression_apply b A hA, sourceBoundaryCompression_apply b A hA]
  exact DFunLike.congr_fun hAA x.val

theorem mem_range_sourceBoundaryCompression_iff (b : BoundaryCondition) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceBoundaryProjection b) A) (hAA : IsIdempotentElem A)
    (x : sourceBoundaryBaseSubspace (p := p) b) :
    x ∈ (sourceBoundaryCompression b A).range ↔ x.val ∈ A.range := by
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨y.val,(sourceBoundaryCompression_apply b A hA y).symm⟩
  · rintro ⟨y,hy⟩
    refine ⟨x,?_⟩
    apply Subtype.ext
    change (sourceBoundaryCompression b A x).val = x.val
    rw [sourceBoundaryCompression_apply b A hA, ← hy]
    exact DFunLike.congr_fun hAA y

/-- The restricted range is isometric to the boundary part of the ambient range. -/
def sourceBoundaryCompressionRangeEquiv (b : BoundaryCondition) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceBoundaryProjection b) A) (hAA : IsIdempotentElem A) :
    (sourceBoundaryCompression b A).range ≃ₗᵢ[ℂ] ↥(A.range ⊓ sourceBoundaryBaseSubspace b) where
  toFun x := ⟨x.val.val, (mem_range_sourceBoundaryCompression_iff b A hA hAA x.val).mp x.property,
    x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2⟩,
    (mem_range_sourceBoundaryCompression_iff b A hA hAA ⟨x.val,x.property.2⟩).mpr x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- Range equivalences identify the rank of the actual original-norm circle restriction. -/
theorem finrank_range_sourceBoundaryCircleProjection (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    Module.finrank ℂ (sourceBoundaryCircleProjection b hp φ c r).range =
      Module.finrank ℂ (b.contourProjection hp (CoeffPair.toMax p φ) c r).range := by
  change Module.finrank ℂ (sourceBoundaryCompression b (sourceResolventCircleIntegral hp φ c r)).range = _
  rw [(sourceBoundaryCompressionRangeEquiv b _
    (sourceBoundaryProjection_commute_circleIntegral b hp φ hφ c r hr hc)
    (sourceResolventCircleIntegral_idempotent hp φ c r hr hc)).toLinearEquiv.finrank_eq,
    sourceResolventCircleIntegral_eq_conj hp φ c r hr hc,
    b.range_contourProjection hp (CoeffPair.toMax p φ) hφ c r hr
      (by rwa [sourceResolventSet_eq] at hc)]
  exact (ConjugatedRanges.rangeInfEquiv (CoeffPair.toMax p) _ (b.space)).finrank_eq

theorem sourceBoundaryProjection_commute_centralIntegral (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    Commute (sourceBoundaryProjection b) (sourceCentralRectangleIntegral hp φ N) := by
  rw [sourceCentralRectangleIntegral_eq_conj hp φ N hc,
    centralRectangleIntegral_eq_centralSpectralProjection hp _ N (by rwa [sourceResolventSet_eq] at hc)]
  exact (b.projection_commute_clusterProjection hp (CoeffPair.toMax p φ) hφ _).map
    ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv)

/-- The central rectangle integral compressed to the selected original boundary space. -/
def sourceBoundaryCentralProjection (b : BoundaryCondition) (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) :
    sourceBoundaryBaseSubspace (p := p) b →L[ℂ] sourceBoundaryBaseSubspace (p := p) b :=
  sourceBoundaryCompression b (sourceCentralRectangleIntegral hp φ N)

/-- Range equivalences identify the rank of the actual original-norm rectangle restriction. -/
theorem finrank_range_sourceBoundaryCentralProjection (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    Module.finrank ℂ (sourceBoundaryCentralProjection b hp φ N).range =
      Module.finrank ℂ (b.centralProjection hp (CoeffPair.toMax p φ) N).range := by
  change Module.finrank ℂ (sourceBoundaryCompression b (sourceCentralRectangleIntegral hp φ N)).range = _
  rw [(sourceBoundaryCompressionRangeEquiv b _
    (sourceBoundaryProjection_commute_centralIntegral b hp φ hφ N hc)
    (sourceCentralRectangleIntegral_idempotent hp φ N hc)).toLinearEquiv.finrank_eq,
    sourceCentralRectangleIntegral_eq_conj hp φ N hc,
    centralRectangleIntegral_eq_centralSpectralProjection hp _ N (by rwa [sourceResolventSet_eq] at hc),
    b.range_centralProjection hp (CoeffPair.toMax p φ) hφ N]
  exact (ConjugatedRanges.rangeInfEquiv (CoeffPair.toMax p) _ (b.space)).finrank_eq

/-- The actual completed interval reflection as a bounded linear map in the original norms. -/
def sourceReflectedPotentialCLM (hp1 : 1 < p) (hp : p ≠ ⊤) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    ((dirichletSubspace (p := p)).subtypeL.comp (periodOneBoundaryPotential hp hp1))

theorem sourceReflectedPotentialCLM_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    sourceReflectedPotentialCLM hp1 hp φ = sourceReflectedPotential hp1 hp φ := by
  apply (CoeffPair.toMax p).injective
  change CoeffPair.toMax p ((CoeffPair.toMax p).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, toMax_sourceReflectedPotential]
  rfl

/-- On an admissible circle, compression agrees with restriction of the actual integral. -/
theorem sourceBoundaryCircleProjection_apply (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) (x : sourceBoundaryBaseSubspace (p := p) b) :
    (sourceBoundaryCircleProjection b hp φ c r x).val = sourceResolventCircleIntegral hp φ c r x.val :=
  sourceBoundaryCompression_apply b _ (sourceBoundaryProjection_commute_circleIntegral b hp φ hφ c r hr hc) x

/-- On an admissible rectangle, compression agrees with restriction of the actual integral. -/
theorem sourceBoundaryCentralProjection_apply (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) (x : sourceBoundaryBaseSubspace (p := p) b) :
    (sourceBoundaryCentralProjection b hp φ N x).val = sourceCentralRectangleIntegral hp φ N x.val :=
  sourceBoundaryCompression_apply b _ (sourceBoundaryProjection_commute_centralIntegral b hp φ hφ N hc) x

/-- The restricted circle integral depends analytically on the original interval input. -/
theorem analyticAt_sourceBoundaryCircleProjection (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp (sourceReflectedPotential hp1 hp φ)) :
    AnalyticAt ℂ (fun ψ => sourceBoundaryCircleProjection b hp (sourceReflectedPotential hp1 hp ψ) c r) φ := by
  have ha := analyticAt_sourceBoundaryCompression (p := p) b
    (sourceResolventCircleIntegral hp (sourceReflectedPotential hp1 hp φ) c r)
  have hf : AnalyticAt ℂ (sourceReflectedPotential hp1 hp) φ := by
    have he : sourceReflectedPotential hp1 hp = sourceReflectedPotentialCLM hp1 hp :=
      funext (fun ψ => (sourceReflectedPotentialCLM_apply hp1 hp ψ).symm)
    rw [he]
    exact (sourceReflectedPotentialCLM hp1 hp).analyticAt φ
  exact ha.comp (f := fun ψ => sourceResolventCircleIntegral hp (sourceReflectedPotential hp1 hp ψ) c r)
    ((analyticAt_sourceResolventCircleIntegral hp _ c r hr hc).comp hf)

/-- A commuting compression has finite rank whenever the ambient operator does. -/
theorem finiteDimensional_range_sourceBoundaryCompression (b : BoundaryCondition)
    (A : CoeffPair p →L[ℂ] CoeffPair p) (hA : Commute (sourceBoundaryProjection b) A)
    [FiniteDimensional ℂ A.range] : FiniteDimensional ℂ (sourceBoundaryCompression b A).range := by
  let C := sourceBoundaryCompression b A
  let f : C.range →ₗ[ℂ] A.range :=
    (((sourceBoundaryBaseSubspace (p := p) b).subtype).comp C.range.subtype).codRestrict A.range (by
      intro x
      obtain ⟨y,hy⟩ := x.property
      refine ⟨y.val,?_⟩
      change A y.val = x.val.val
      rw [← sourceBoundaryCompression_apply b A hA y]
      exact congrArg Subtype.val hy)
  apply FiniteDimensional.of_injective f
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : A.range => z.val) h

/-- The actual circle restriction is a finite-rank projection. -/
theorem sourceBoundaryCircleProjection_properties (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    IsIdempotentElem (sourceBoundaryCircleProjection b hp φ c r) ∧
      FiniteDimensional ℂ (sourceBoundaryCircleProjection b hp φ c r).range := by
  have hcomm := sourceBoundaryProjection_commute_circleIntegral b hp φ hφ c r hr hc
  let := finiteDimensional_range_sourceResolventCircleIntegral hp φ c r hr hc
  exact ⟨sourceBoundaryCompression_idempotent b _ hcomm
    (sourceResolventCircleIntegral_idempotent hp φ c r hr hc),
    finiteDimensional_range_sourceBoundaryCompression b _ hcomm⟩

/-- The actual four-edge rectangle restriction is a finite-rank projection. -/
theorem sourceBoundaryCentralProjection_properties (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    IsIdempotentElem (sourceBoundaryCentralProjection b hp φ N) ∧
      FiniteDimensional ℂ (sourceBoundaryCentralProjection b hp φ N).range := by
  have hcomm := sourceBoundaryProjection_commute_centralIntegral b hp φ hφ N hc
  let := finiteDimensional_range_sourceCentralRectangleIntegral hp φ N hc
  exact ⟨sourceBoundaryCompression_idempotent b _ hcomm
    (sourceCentralRectangleIntegral_idempotent hp φ N hc),
    finiteDimensional_range_sourceBoundaryCompression b _ hcomm⟩

/-- Restricting a norm-analytic family of actual central integrals preserves analyticity. -/
theorem analyticAt_sourceBoundaryCentralProjection_of_integral (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (N : ℕ)
    (ha : AnalyticAt ℂ (fun ψ => sourceCentralRectangleIntegral hp ψ N) φ) :
    AnalyticAt ℂ (fun ψ => sourceBoundaryCentralProjection b hp ψ N) φ :=
  (analyticAt_sourceBoundaryCompression b _).comp
    (f := fun ψ => sourceCentralRectangleIntegral hp ψ N) ha

end NLS.ZakharovShabat
