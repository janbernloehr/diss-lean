import NLS.ZakharovShabat.AuxiliaryContourPhase
import NLS.ZakharovShabat.SourceContourRanks

/-!
# Original auxiliary restrictions of the Cauchy–Riesz integrals

The operators here act on the original auxiliary base spaces. On admissible
contours they are the actual restrictions of the normalized circle and
four-edge rectangle integrals, with range equal to the auxiliary part of the
ambient range. Continuous range equivalences preserve ranks without assuming
an isometry between the original norm and the auxiliary maximum norm.
-/

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complementary auxiliary projection in the original component-sum norm. -/
def sourceAuxiliaryProjection (b : BoundaryCondition) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.conjContinuousAlgEquiv (b.auxiliaryProjection)

theorem sourceAuxiliaryProjection_mem (b : BoundaryCondition) (a : CoeffPair p) :
    sourceAuxiliaryProjection b a ∈ auxiliarySourceSpace b := by
  change CoeffPair.toMax p ((CoeffPair.toMax p).symm (b.auxiliaryProjection (CoeffPair.toMax p a))) ∈ b.auxiliarySpace
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact b.auxiliaryProjection_mem _

theorem sourceAuxiliaryProjection_eq_self (b : BoundaryCondition) (a : CoeffPair p)
    (ha : a ∈ auxiliarySourceSpace b) : sourceAuxiliaryProjection b a = a := by
  change (CoeffPair.toMax p).symm (b.auxiliaryProjection (CoeffPair.toMax p a)) = a
  have he : b.auxiliaryProjection (CoeffPair.toMax p a) = CoeffPair.toMax p a := b.auxiliaryProjection_eq_self _ ha
  rw [he, ContinuousLinearEquiv.symm_apply_apply]

private def auxiliaryGenericCompression {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Submodule ℂ E) (Q : E →L[ℂ] S) :
    (E →L[ℂ] E) →L[ℂ] (S →L[ℂ] S) :=
  ((ContinuousLinearMap.compL ℂ S E S).flip S.subtypeL).comp
    ((ContinuousLinearMap.compL ℂ E E S) Q)

private theorem auxiliaryGenericCompression_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Submodule ℂ E) (Q : E →L[ℂ] S) (A : E →L[ℂ] E) :
    AnalyticAt ℂ (auxiliaryGenericCompression S Q) A := ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := E →L[ℂ] E)
    (F := S →L[ℂ] S) (auxiliaryGenericCompression S Q) A

/-- Bounded compression; for commuting operators this is their actual restriction. -/
def sourceAuxiliaryCompression (b : BoundaryCondition) :
    (CoeffPair p →L[ℂ] CoeffPair p) →L[ℂ]
      (auxiliarySourceSpace (p := p) b →L[ℂ] auxiliarySourceSpace (p := p) b) :=
  auxiliaryGenericCompression (E := CoeffPair p) (auxiliarySourceSpace (p := p) b)
    ((sourceAuxiliaryProjection b).codRestrict _ (sourceAuxiliaryProjection_mem b))

theorem analyticAt_sourceAuxiliaryCompression (b : BoundaryCondition) (A : CoeffPair p →L[ℂ] CoeffPair p) :
    AnalyticAt ℂ (sourceAuxiliaryCompression b) A := auxiliaryGenericCompression_analytic _ _ A

theorem sourceAuxiliaryCompression_apply (b : BoundaryCondition) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceAuxiliaryProjection b) A) (x : auxiliarySourceSpace (p := p) b) :
    (sourceAuxiliaryCompression b A x).val = A x.val := by
  change sourceAuxiliaryProjection b (A x.val) = A x.val
  have h := DFunLike.congr_fun hA.eq x.val
  change sourceAuxiliaryProjection b (A x.val) = A (sourceAuxiliaryProjection b x.val) at h
  rw [h, sourceAuxiliaryProjection_eq_self b x.val x.property]

theorem sourceAuxiliaryProjection_commute_circleIntegral (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    Commute (sourceAuxiliaryProjection b) (sourceResolventCircleIntegral hp φ c r) := by
  rw [sourceResolventCircleIntegral_eq_conj hp φ c r hr hc]
  exact (b.auxiliaryProjection_commute_circleIntegral hp (CoeffPair.toMax p φ) hφ c r hr
    (by rwa [sourceResolventSet_eq] at hc)).map ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv)

/-- The circle integral compressed to the selected original auxiliary space. -/
def sourceAuxiliaryCircleProjection (b : BoundaryCondition) (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (r : ℝ) :
    auxiliarySourceSpace (p := p) b →L[ℂ] auxiliarySourceSpace (p := p) b :=
  sourceAuxiliaryCompression b (sourceResolventCircleIntegral hp φ c r)

theorem sourceAuxiliaryCompression_idempotent (b : BoundaryCondition) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceAuxiliaryProjection b) A) (hAA : IsIdempotentElem A) :
    IsIdempotentElem (sourceAuxiliaryCompression b A) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change (sourceAuxiliaryCompression b A (sourceAuxiliaryCompression b A x)).val =
    (sourceAuxiliaryCompression b A x).val
  rw [sourceAuxiliaryCompression_apply b A hA, sourceAuxiliaryCompression_apply b A hA]
  exact DFunLike.congr_fun hAA x.val

theorem mem_range_sourceAuxiliaryCompression_iff (b : BoundaryCondition) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceAuxiliaryProjection b) A) (hAA : IsIdempotentElem A)
    (x : auxiliarySourceSpace (p := p) b) :
    x ∈ (sourceAuxiliaryCompression b A).range ↔ x.val ∈ A.range := by
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨y.val,(sourceAuxiliaryCompression_apply b A hA y).symm⟩
  · rintro ⟨y,hy⟩
    refine ⟨x,?_⟩
    apply Subtype.ext
    change (sourceAuxiliaryCompression b A x).val = x.val
    rw [sourceAuxiliaryCompression_apply b A hA, ← hy]
    exact DFunLike.congr_fun hAA y

/-- The restricted range is isometric to the auxiliary part of the ambient range. -/
def sourceAuxiliaryCompressionRangeEquiv (b : BoundaryCondition) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceAuxiliaryProjection b) A) (hAA : IsIdempotentElem A) :
    (sourceAuxiliaryCompression b A).range ≃ₗᵢ[ℂ] ↥(A.range ⊓ auxiliarySourceSpace b) where
  toFun x := ⟨x.val.val, (mem_range_sourceAuxiliaryCompression_iff b A hA hAA x.val).mp x.property,
    x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2⟩,
    (mem_range_sourceAuxiliaryCompression_iff b A hA hAA ⟨x.val,x.property.2⟩).mpr x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

theorem sourceAuxiliaryProjection_commute_centralIntegral (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    Commute (sourceAuxiliaryProjection b) (sourceCentralRectangleIntegral hp φ N) := by
  rw [sourceCentralRectangleIntegral_eq_conj hp φ N hc]
  exact (b.auxiliaryProjection_commute_centralIntegral hp (CoeffPair.toMax p φ) hφ N
    (by rwa [sourceResolventSet_eq] at hc)).map ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv)

/-- The central rectangle integral compressed to the selected original auxiliary space. -/
def sourceAuxiliaryCentralProjection (b : BoundaryCondition) (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) :
    auxiliarySourceSpace (p := p) b →L[ℂ] auxiliarySourceSpace (p := p) b :=
  sourceAuxiliaryCompression b (sourceCentralRectangleIntegral hp φ N)

/-- The actual completed interval reflection as a bounded linear map in the original norms. -/
def sourceAuxiliaryReflectedPotentialCLM (hp1 : 1 < p) (hp : p ≠ ⊤) : CoeffPair p →L[ℂ] CoeffPair p :=
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp
    ((neumannSubspace (p := p)).subtypeL.comp (auxiliaryPeriodOnePotential hp hp1))

theorem sourceAuxiliaryReflectedPotentialCLM_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    sourceAuxiliaryReflectedPotentialCLM hp1 hp φ = sourceAuxiliaryReflectedPotential hp1 hp φ := by
  apply (CoeffPair.toMax p).injective
  change CoeffPair.toMax p ((CoeffPair.toMax p).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, toMax_sourceAuxiliaryReflectedPotential]
  rfl

/-- On an admissible circle, compression agrees with restriction of the actual integral. -/
theorem sourceAuxiliaryCircleProjection_apply (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) (x : auxiliarySourceSpace (p := p) b) :
    (sourceAuxiliaryCircleProjection b hp φ c r x).val = sourceResolventCircleIntegral hp φ c r x.val :=
  sourceAuxiliaryCompression_apply b _ (sourceAuxiliaryProjection_commute_circleIntegral b hp φ hφ c r hr hc) x

/-- On an admissible rectangle, compression agrees with restriction of the actual integral. -/
theorem sourceAuxiliaryCentralProjection_apply (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) (x : auxiliarySourceSpace (p := p) b) :
    (sourceAuxiliaryCentralProjection b hp φ N x).val = sourceCentralRectangleIntegral hp φ N x.val :=
  sourceAuxiliaryCompression_apply b _ (sourceAuxiliaryProjection_commute_centralIntegral b hp φ hφ N hc) x

/-- The restricted circle integral depends analytically on the original interval input. -/
theorem analyticAt_sourceAuxiliaryCircleProjection (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp (sourceAuxiliaryReflectedPotential hp1 hp φ)) :
    AnalyticAt ℂ (fun ψ => sourceAuxiliaryCircleProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) c r) φ := by
  have ha := analyticAt_sourceAuxiliaryCompression (p := p) b
    (sourceResolventCircleIntegral hp (sourceAuxiliaryReflectedPotential hp1 hp φ) c r)
  have hf : AnalyticAt ℂ (sourceAuxiliaryReflectedPotential hp1 hp) φ := by
    have he : sourceAuxiliaryReflectedPotential hp1 hp = sourceAuxiliaryReflectedPotentialCLM hp1 hp :=
      funext (fun ψ => (sourceAuxiliaryReflectedPotentialCLM_apply hp1 hp ψ).symm)
    rw [he]
    exact (sourceAuxiliaryReflectedPotentialCLM hp1 hp).analyticAt φ
  exact ha.comp (f := fun ψ => sourceResolventCircleIntegral hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) c r)
    ((analyticAt_sourceResolventCircleIntegral hp _ c r hr hc).comp hf)

/-- A commuting compression has finite rank whenever the ambient operator does. -/
theorem finiteDimensional_range_sourceAuxiliaryCompression (b : BoundaryCondition)
    (A : CoeffPair p →L[ℂ] CoeffPair p) (hA : Commute (sourceAuxiliaryProjection b) A)
    [FiniteDimensional ℂ A.range] : FiniteDimensional ℂ (sourceAuxiliaryCompression b A).range := by
  let C := sourceAuxiliaryCompression b A
  let f : C.range →ₗ[ℂ] A.range :=
    (((auxiliarySourceSpace (p := p) b).subtype).comp C.range.subtype).codRestrict A.range (by
      intro x
      obtain ⟨y,hy⟩ := x.property
      refine ⟨y.val,?_⟩
      change A y.val = x.val.val
      rw [← sourceAuxiliaryCompression_apply b A hA y]
      exact congrArg Subtype.val hy)
  apply FiniteDimensional.of_injective f
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : A.range => z.val) h

/-- The actual circle restriction is a finite-rank projection. -/
theorem sourceAuxiliaryCircleProjection_properties (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    IsIdempotentElem (sourceAuxiliaryCircleProjection b hp φ c r) ∧
      FiniteDimensional ℂ (sourceAuxiliaryCircleProjection b hp φ c r).range := by
  have hcomm := sourceAuxiliaryProjection_commute_circleIntegral b hp φ hφ c r hr hc
  let := finiteDimensional_range_sourceResolventCircleIntegral hp φ c r hr hc
  exact ⟨sourceAuxiliaryCompression_idempotent b _ hcomm
    (sourceResolventCircleIntegral_idempotent hp φ c r hr hc),
    finiteDimensional_range_sourceAuxiliaryCompression b _ hcomm⟩

/-- The actual four-edge rectangle restriction is a finite-rank projection. -/
theorem sourceAuxiliaryCentralProjection_properties (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    IsIdempotentElem (sourceAuxiliaryCentralProjection b hp φ N) ∧
      FiniteDimensional ℂ (sourceAuxiliaryCentralProjection b hp φ N).range := by
  have hcomm := sourceAuxiliaryProjection_commute_centralIntegral b hp φ hφ N hc
  let := finiteDimensional_range_sourceCentralRectangleIntegral hp φ N hc
  exact ⟨sourceAuxiliaryCompression_idempotent b _ hcomm
    (sourceCentralRectangleIntegral_idempotent hp φ N hc),
    finiteDimensional_range_sourceAuxiliaryCompression b _ hcomm⟩

/-- Restricting a norm-analytic family of actual central integrals preserves analyticity. -/
theorem analyticAt_sourceAuxiliaryCentralProjection_of_integral (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (N : ℕ)
    (ha : AnalyticAt ℂ (fun ψ => sourceCentralRectangleIntegral hp ψ N) φ) :
    AnalyticAt ℂ (fun ψ => sourceAuxiliaryCentralProjection b hp ψ N) φ :=
  (analyticAt_sourceAuxiliaryCompression b _).comp
    (f := fun ψ => sourceCentralRectangleIntegral hp ψ N) ha

end NLS.ZakharovShabat
