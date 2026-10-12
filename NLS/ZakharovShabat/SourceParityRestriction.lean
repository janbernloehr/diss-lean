import NLS.ZakharovShabat.SourceLemma3_6
/-! # Actual contour restrictions on the original-norm parity subspaces

Even potentials give invariant parity subspaces for every admissible circle
and central rectangle. The resulting operators have those subspaces as both
domain and codomain, agree there with the original contour integrals, and
are idempotent with finite-dimensional range. Bounded compression transfers
analytic dependence to the restricted operators.
-/
noncomputable section

open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def genericCompression {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Submodule ℂ E) (Q : E →L[ℂ] S) :
    (E →L[ℂ] E) →L[ℂ] (S →L[ℂ] S) :=
  ((ContinuousLinearMap.compL ℂ S E S).flip S.subtypeL).comp
    ((ContinuousLinearMap.compL ℂ E E S) Q)

private theorem genericCompression_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Submodule ℂ E) (Q : E →L[ℂ] S) (A : E →L[ℂ] E) :
    AnalyticAt ℂ (genericCompression S Q) A := ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := E →L[ℂ] E)
    (F := S →L[ℂ] S) (genericCompression S Q) A

/-- A bounded operation from ambient operators to endomorphisms of a parity subspace.
For commuting operators, this is their actual restriction. -/
def sourceParityCompression (r : ℤ) :
    (CoeffPair p →L[ℂ] CoeffPair p) →L[ℂ]
      (sourceParitySubspace (p := p) r →L[ℂ] sourceParitySubspace (p := p) r) :=
  genericCompression (E := CoeffPair p) (sourceParitySubspace (p := p) r)
    ((sourceParityProjection (p := p) r).codRestrict (sourceParitySubspace r) (sourceParityProjection_mem r))

theorem sourceParityCompression_apply (r : ℤ) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceParityProjection r) A) (x : sourceParitySubspace (p := p) r) :
    (sourceParityCompression r A x).val = A x.val := by
  change sourceParityProjection r (A x.val) = A x.val
  have h := DFunLike.congr_fun hA.eq x.val
  change sourceParityProjection r (A x.val) = A (sourceParityProjection r x.val) at h
  rw [h, (sourceParityProjection_eq_self_iff r x.val).mpr x.property]

theorem sourceParityCompression_idempotent (r : ℤ) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceParityProjection r) A) (hAA : IsIdempotentElem A) :
    IsIdempotentElem (sourceParityCompression r A) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change (sourceParityCompression r A (sourceParityCompression r A x)).val = (sourceParityCompression r A x).val
  rw [sourceParityCompression_apply r A hA, sourceParityCompression_apply r A hA]
  exact DFunLike.congr_fun hAA x.val

theorem sourceParityProjection_commute_rectangleIntegral (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z w : ℂ)
    (hc : RectangleIntegral.boundary z w ⊆ sourceResolventSet hp φ) :
    Commute (sourceParityProjection r) (sourceResolventRectangleIntegral hp φ z w) := by
  rw [sourceResolventRectangleIntegral_eq_conj hp φ z w hc]
  have hc' : RectangleIntegral.boundary z w ⊆ resolventSet hp (CoeffPair.toMax p φ) := by
    rwa [sourceResolventSet_eq] at hc
  exact (commute_resolventRectangleIntegral hp (CoeffPair.toMax p φ) z w hc' _
    (fun ζ hζ => pairParityProjection_commute_resolvent hp (CoeffPair.toMax p φ) hφ r ζ (hc' hζ))).map
      ((CoeffPair.toMax p).symm.conjContinuousAlgEquiv)

/-- The restricted range is exactly the parity part of an ambient projection's range. -/
theorem mem_range_sourceParityCompression_iff (r : ℤ) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceParityProjection r) A) (hAA : IsIdempotentElem A)
    (x : sourceParitySubspace (p := p) r) :
    x ∈ (sourceParityCompression r A).range ↔ x.val ∈ A.range := by
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨y.val,(sourceParityCompression_apply r A hA y).symm⟩
  · rintro ⟨y,hy⟩
    refine ⟨x,?_⟩
    apply Subtype.ext
    change (sourceParityCompression r A x).val = x.val
    rw [sourceParityCompression_apply r A hA, ← hy]
    exact DFunLike.congr_fun hAA y

/-- Compression is analytic as a function of the ambient bounded operator. -/
theorem analyticAt_sourceParityCompression (r : ℤ) (A : CoeffPair p →L[ℂ] CoeffPair p) :
    AnalyticAt ℂ (sourceParityCompression (p := p) r) A :=
  genericCompression_analytic _ _ A

theorem sourceParityProjection_commute_centralIntegral (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    Commute (sourceParityProjection r) (sourceCentralRectangleIntegral hp φ N) :=
  sourceParityProjection_commute_rectangleIntegral hp φ hφ r _ _
    (by rwa [centralCorner_boundary])

/-- Circle projector on a parity subspace. On even potentials and admissible circles
this is the restriction in equation (1.5), as `sourceParityCircleProjection_apply` proves. -/
def sourceParityCircleProjection (hp : p ≠ ⊤) (φ : CoeffPair p) (c : ℂ) (R : ℝ) (r : ℤ) :
    sourceParitySubspace (p := p) r →L[ℂ] sourceParitySubspace (p := p) r :=
  sourceParityCompression r (sourceResolventCircleIntegral hp φ c R)

/-- Central rectangular projector on a parity subspace, with the same restriction interpretation. -/
def sourceParityCentralProjection (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) (r : ℤ) :
    sourceParitySubspace (p := p) r →L[ℂ] sourceParitySubspace (p := p) r :=
  sourceParityCompression r (sourceCentralRectangleIntegral hp φ N)

theorem sourceParityCircleProjection_apply (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ) (hR : 0 ≤ R)
    (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) (x : sourceParitySubspace (p := p) r) :
    (sourceParityCircleProjection hp φ c R r x).val = sourceResolventCircleIntegral hp φ c R x.val :=
  sourceParityCompression_apply r _ (sourceParityProjection_commute_circleIntegral hp φ hφ r c R hR hc) x

theorem sourceParityCentralProjection_apply (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (N : ℕ) (r : ℤ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) (x : sourceParitySubspace (p := p) r) :
    (sourceParityCentralProjection hp φ N r x).val = sourceCentralRectangleIntegral hp φ N x.val :=
  sourceParityCompression_apply r _ (sourceParityProjection_commute_centralIntegral hp φ hφ r N hc) x

theorem sourceParityCircleProjection_idempotent (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ) (hR : 0 ≤ R)
    (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    IsIdempotentElem (sourceParityCircleProjection hp φ c R r) :=
  sourceParityCompression_idempotent r _
    (sourceParityProjection_commute_circleIntegral hp φ hφ r c R hR hc)
    (sourceResolventCircleIntegral_idempotent hp φ c R hR hc)

theorem sourceParityCentralProjection_idempotent (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (N : ℕ) (r : ℤ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    IsIdempotentElem (sourceParityCentralProjection hp φ N r) :=
  sourceParityCompression_idempotent r _
    (sourceParityProjection_commute_centralIntegral hp φ hφ r N hc)
    (sourceCentralRectangleIntegral_idempotent hp φ N hc)

/-- Restriction preserves finite rank when the ambient operator commutes with parity. -/
theorem finiteDimensional_range_sourceParityCompression (r : ℤ) (A : CoeffPair p →L[ℂ] CoeffPair p)
    (hA : Commute (sourceParityProjection r) A) [FiniteDimensional ℂ A.range] :
    FiniteDimensional ℂ (sourceParityCompression r A).range := by
  let C := sourceParityCompression r A
  let f : C.range →ₗ[ℂ] A.range :=
    (((sourceParitySubspace (p := p) r).subtype).comp C.range.subtype).codRestrict A.range (by
      intro x
      obtain ⟨y,hy⟩ := x.property
      refine ⟨y.val,?_⟩
      change A y.val = x.val.val
      rw [← sourceParityCompression_apply r A hA y]
      exact congrArg Subtype.val hy)
  apply FiniteDimensional.of_injective f
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : A.range => z.val) h

theorem finiteDimensional_range_sourceParityCircleProjection (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ) (hR : 0 ≤ R)
    (hc : Metric.sphere c R ⊆ sourceResolventSet hp φ) :
    FiniteDimensional ℂ (sourceParityCircleProjection hp φ c R r).range := by
  let := finiteDimensional_range_sourceResolventCircleIntegral hp φ c R hR hc
  exact finiteDimensional_range_sourceParityCompression r _
    (sourceParityProjection_commute_circleIntegral hp φ hφ r c R hR hc)

theorem finiteDimensional_range_sourceParityCentralProjection (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (N : ℕ) (r : ℤ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    FiniteDimensional ℂ (sourceParityCentralProjection hp φ N r).range := by
  let := finiteDimensional_range_sourceCentralRectangleIntegral hp φ N hc
  exact finiteDimensional_range_sourceParityCompression r _
    (sourceParityProjection_commute_centralIntegral hp φ hφ r N hc)

/-- Local analytic dependence in the original period-one potential coordinates. -/
theorem analyticAt_sourceParityCircleProjection (hp : p ≠ ⊤) (φ : CoeffPair p)
    (c : ℂ) (R : ℝ) (r : ℤ) (hR : 0 ≤ R)
    (hc : Metric.sphere c R ⊆ sourceResolventSet hp (periodOnePair φ)) :
    AnalyticAt ℂ (fun ψ => sourceParityCircleProjection hp (periodOnePair ψ) c R r) φ :=
  (analyticAt_sourceParityCompression r _).comp
    ((analyticAt_sourceResolventCircleIntegral hp (periodOnePair φ) c R hR hc).comp
      ((periodOnePair (p := p)).toContinuousLinearMap.analyticAt φ))

end NLS.ZakharovShabat
