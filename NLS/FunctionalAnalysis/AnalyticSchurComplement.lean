import NLS.FunctionalAnalysis.SchurComplement
import NLS.FunctionalAnalysis.FiniteSpectralDeterminant

/-! # Analytic determinants detecting invertibility of block operators -/
noncomputable section
open Filter Topology Set
namespace NLS.SchurComplement
variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The total Schur expression, using the ring inverse of the lower block. -/
def expression (A : E →L[ℂ] E) (B : F →L[ℂ] E) (C : E →L[ℂ] F) (D : F →L[ℂ] F) :
    E →L[ℂ] E := A - B.comp ((Ring.inverse D).comp C)

omit [CompleteSpace F] in
/-- Composition of two analytic bounded-operator families is analytic. -/
theorem analyticAt_compCLM {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {A : X → F →L[ℂ] G} {B : X → E →L[ℂ] F} {x : X}
    (hA : AnalyticAt ℂ A x) (hB : AnalyticAt ℂ B x) :
    AnalyticAt ℂ (fun y => (A y).comp (B y)) x :=
  ((ContinuousLinearMap.compL ℂ E F G).analyticAt_bilinear (A x,B x)).comp
    (f := fun y => (A y,B y)) (hA.prod hB)

/-- The Schur expression is analytic wherever its lower block is invertible. -/
theorem analyticAt_expression {A : X → E →L[ℂ] E} {B : X → F →L[ℂ] E}
    {C : X → E →L[ℂ] F} {D : X → F →L[ℂ] F} {x : X}
    (hA : AnalyticAt ℂ A x) (hB : AnalyticAt ℂ B x)
    (hC : AnalyticAt ℂ C x) (hD : AnalyticAt ℂ D x) (hu : IsUnit (D x)) :
    AnalyticAt ℂ (fun y => expression (A y) (B y) (C y) (D y)) x := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ) _ hu).comp hD
  exact hA.sub (analyticAt_compCLM hB (analyticAt_compCLM hi hC))

variable [FiniteDimensional ℂ E]

/-- A finite Schur determinant detects exactly the invertible full operators. -/
theorem isUnit_block_iff_det_ne_zero (A : E →L[ℂ] E) (B : F →L[ℂ] E)
    (C : E →L[ℂ] F) (D : F →L[ℂ] F) (hu : IsUnit D) :
    IsUnit (block A B C D) ↔ (expression A B C D).toLinearMap.det ≠ 0 := by
  obtain ⟨u,rfl⟩ := hu
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have h := bijective_block_iff A B C (ContinuousLinearEquiv.ofUnit u)
  change Function.Bijective (block A B C (u : F →L[ℂ] F)) ↔ _ at h
  rw [h, ← ContinuousLinearMap.isUnit_iff_bijective,
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_isUnit_det]
  simp only [expression,schur,Ring.inverse_unit,isUnit_iff_ne_zero]
  rfl

/-- Locally, a single analytic scalar function detects all singular members
of a block family. The center itself may be singular. -/
theorem exists_local_analytic_determinant
    {A : X → E →L[ℂ] E} {B : X → F →L[ℂ] E}
    {C : X → E →L[ℂ] F} {D : X → F →L[ℂ] F} {x : X}
    (hA : AnalyticAt ℂ A x) (hB : AnalyticAt ℂ B x)
    (hC : AnalyticAt ℂ C x) (hD : AnalyticAt ℂ D x) (hu : IsUnit (D x)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ d : X → ℂ,
      AnalyticOnNhd ℂ d U ∧ ∀ y ∈ U, IsUnit (block (A y) (B y) (C y) (D y)) ↔ d y ≠ 0 := by
  let d := fun y => (expression (A y) (B y) (C y) (D y)).toLinearMap.det
  have hd : AnalyticAt ℂ d x := FiniteSpectralDeterminant.analyticAt_det
    (analyticAt_expression hA hB hC hD hu)
  have hunit : ∀ᶠ y in 𝓝 x, IsUnit (D y) :=
    hD.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hu)
  obtain ⟨V,hV,hVU,hx⟩ := mem_nhds_iff.mp hunit
  refine ⟨V ∩ {y | AnalyticAt ℂ d y}, hVU.inter (isOpen_analyticAt ℂ d),⟨hx,hd⟩,d,?_,?_⟩
  · intro y hy
    exact hy.2
  · intro y hy
    exact isUnit_block_iff_det_ne_zero _ _ _ _ (hV hy.1)

end NLS.SchurComplement
